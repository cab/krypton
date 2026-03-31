#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.12"
# dependencies = ["markdown", "jinja2", "watchdog"]
# ///

"""Static site generator for the Krypton language tour."""

import argparse
import functools
import html
import http.server
import re
import shutil
import subprocess
import threading
import time
from pathlib import Path

import markdown
from jinja2 import Environment, FileSystemLoader

ROOT = Path(__file__).parent
WORKSPACE_ROOT = ROOT.parent
CONTENT = ROOT / "content"
TEMPLATES = ROOT / "templates"
STATIC = ROOT / "static"
FRONTEND = ROOT / "frontend"
GENERATED = ROOT / "generated"
DIST = ROOT / "dist"
RUNTIME_JS = WORKSPACE_ROOT / "runtime" / "js"
STDLIB = WORKSPACE_ROOT / "stdlib"
WASM_INPUT_DIRS = [
    WORKSPACE_ROOT / "crates" / "playground",
    WORKSPACE_ROOT / "crates" / "codegen_js",
    WORKSPACE_ROOT / "crates" / "modules",
    WORKSPACE_ROOT / "crates" / "parser",
    WORKSPACE_ROOT / "crates" / "typechecker",
    WORKSPACE_ROOT / "crates" / "ir",
    RUNTIME_JS,
    STDLIB,
]
ROOT_WATCH_FILES = {
    (WORKSPACE_ROOT / "Cargo.toml").resolve(),
    (WORKSPACE_ROOT / "Cargo.lock").resolve(),
}
REQUIRED_FRONTEND_ASSETS = [
    GENERATED / "tour.js",
    GENERATED / "playground-worker.js",
]
KRYPTON_FENCE_LANGUAGES = {"krypton", "kr"}
SNIPPET_PLACEHOLDER_RE = re.compile(
    r"<div class=\"krypton-snippet-placeholder\" data-snippet=\"(?P<index>\d+)\"></div>"
)


def resolved_path(path: Path) -> Path:
    try:
        return path.resolve()
    except FileNotFoundError:
        return path


def build_frontend():
    """Bundle the frontend editor code."""
    GENERATED.mkdir(exist_ok=True)
    try:
        subprocess.run(["npm", "run", "build:frontend"], cwd=ROOT, check=True)
    except FileNotFoundError as exc:
        raise RuntimeError("npm is required to build the book frontend.") from exc


def build_playground_wasm(release: bool = True):
    """Build the wasm playground package into generated/compiler/."""
    GENERATED.mkdir(exist_ok=True)
    try:
        task = "build:playground-wasm:release" if release else "build:playground-wasm"
        subprocess.run(["npm", "run", task], cwd=ROOT, check=True)
    except FileNotFoundError as exc:
        raise RuntimeError(
            "wasm-pack is required to build the playground compiler."
        ) from exc


def ensure_generated_frontend_assets():
    """Fail clearly when the generated frontend bundle is missing."""
    missing = [path.name for path in REQUIRED_FRONTEND_ASSETS if not path.exists()]
    if missing:
        assets = ", ".join(missing)
        raise RuntimeError(
            f"Missing generated frontend assets: {assets}. "
            "Run `npm run build:frontend` from book/ before rendering the site."
        )


def slug_from_dir(name: str) -> str:
    """Strip numeric prefix and convert underscores to hyphens."""
    # Remove chNN_ or NN_ prefix
    parts = name.split("_", 1) if not name.startswith("ch") else name.split("_", 1)
    rest = parts[1] if len(parts) > 1 else parts[0]
    return rest.replace("_", "-")


def title_from_dir(name: str) -> str:
    """Strip numeric prefix and convert to title case."""
    parts = name.split("_", 1) if not name.startswith("ch") else name.split("_", 1)
    rest = parts[1] if len(parts) > 1 else parts[0]
    return rest.replace("_", " ").title()


def classify_krypton_fence(info: str) -> str | None:
    tokens = info.split()
    if not tokens or tokens[0].lower() not in KRYPTON_FENCE_LANGUAGES:
        return None
    if any(token.lower() == "static" for token in tokens[1:]):
        return "static"
    return "runnable"


def parse_lesson_markdown(source: str) -> tuple[str, list[dict[str, str]]]:
    rendered_parts = []
    snippets = []
    lines = source.splitlines(keepends=True)
    i = 0

    while i < len(lines):
        line = lines[i]
        if not line.startswith("```"):
            rendered_parts.append(line)
            i += 1
            continue

        info = line[3:].strip()
        mode = classify_krypton_fence(info)
        if mode is None:
            rendered_parts.append(line)
            i += 1
            continue

        code_lines = []
        i += 1
        while i < len(lines) and not lines[i].startswith("```"):
            code_lines.append(lines[i])
            i += 1

        if i >= len(lines):
            rendered_parts.append(line)
            rendered_parts.extend(code_lines)
            break

        snippet_index = len(snippets)
        snippets.append({"mode": mode, "code": "".join(code_lines).rstrip("\n")})
        rendered_parts.append(
            f'<div class="krypton-snippet-placeholder" data-snippet="{snippet_index}"></div>\n'
        )
        i += 1

    return "".join(rendered_parts), snippets


def render_snippet_html(mode: str, code: str) -> str:
    escaped_code = html.escape(code)
    if mode == "static":
        return (
            '<div class="code-block code-block-static" data-code-mode="static">'
            f'<textarea class="editor" aria-label="Static Krypton code">{escaped_code}</textarea>'
            "</div>"
        )

    return (
        '<div class="code-block code-block-runnable" data-code-mode="runnable">'
        f'<textarea class="editor" aria-label="Runnable Krypton code">{escaped_code}</textarea>'
        '<div class="code-controls"><button class="run-btn">Run</button></div>'
        '<div class="output"><pre class="output-text"></pre></div>'
        "</div>"
    )


def render_lesson_prose(source: str) -> str:
    processed_markdown, snippets = parse_lesson_markdown(source)
    rendered_html = markdown.markdown(processed_markdown, extensions=["fenced_code"])

    def replace_placeholder(match: re.Match[str]) -> str:
        snippet = snippets[int(match.group("index"))]
        return render_snippet_html(snippet["mode"], snippet["code"])

    return SNIPPET_PLACEHOLDER_RE.sub(replace_placeholder, rendered_html)


def discover_content():
    """Walk content/ and return structured chapter/lesson data."""
    chapters = []
    for ch_dir in sorted(CONTENT.iterdir()):
        if not ch_dir.is_dir() or not ch_dir.name.startswith("ch"):
            continue
        chapter = {
            "dir_name": ch_dir.name,
            "title": title_from_dir(ch_dir.name),
            "slug": slug_from_dir(ch_dir.name),
            "lessons": [],
        }
        for lesson_file in sorted(ch_dir.iterdir()):
            if lesson_file.is_dir() or lesson_file.suffix != ".md":
                continue
            lesson_name = lesson_file.stem
            lesson = {
                "source_name": lesson_name,
                "title": title_from_dir(lesson_name),
                "slug": slug_from_dir(lesson_name),
                "prose": render_lesson_prose(lesson_file.read_text()),
                "chapter": chapter,
            }
            lesson["url"] = f"/guide/{chapter['slug']}/{lesson['slug']}/"
            chapter["lessons"].append(lesson)
        if chapter["lessons"]:
            chapters.append(chapter)
    return chapters


def render_site():
    ensure_generated_frontend_assets()
    env = Environment(loader=FileSystemLoader(TEMPLATES))
    chapters = discover_content()

    # Flatten lessons for prev/next
    all_lessons = [l for ch in chapters for l in ch["lessons"]]
    for i, lesson in enumerate(all_lessons):
        lesson["prev"] = all_lessons[i - 1] if i > 0 else None
        lesson["next"] = all_lessons[i + 1] if i < len(all_lessons) - 1 else None

    # Clean dist
    if DIST.exists():
        shutil.rmtree(DIST)
    DIST.mkdir()

    # Copy static files
    shutil.copytree(STATIC, DIST / "static")
    for generated_file in GENERATED.iterdir():
        target = DIST / "static" / generated_file.name
        if generated_file.is_file():
            shutil.copy2(generated_file, target)
        elif generated_file.is_dir():
            shutil.copytree(generated_file, target)

    # Render home page
    home_tmpl = env.get_template("home.html")
    (DIST / "index.html").write_text(
        home_tmpl.render(
            title="Home",
            chapters=chapters,
        )
    )

    # Render lesson pages
    lesson_tmpl = env.get_template("lesson.html")
    for lesson in all_lessons:
        ch_slug = lesson["chapter"]["slug"]
        l_slug = lesson["slug"]
        out_dir = DIST / "guide" / ch_slug / l_slug
        out_dir.mkdir(parents=True, exist_ok=True)
        (out_dir / "index.html").write_text(
            lesson_tmpl.render(
                title=lesson["title"],
                lesson=lesson,
                chapters=chapters,
            )
        )

    print(f"Built {len(all_lessons)} lessons in {len(chapters)} chapters → dist/")


def build(
    *, release: bool = True, include_frontend: bool = True, include_wasm: bool = True
):
    if include_frontend:
        build_frontend()
    if include_wasm:
        build_playground_wasm(release=release)
    render_site()


def should_ignore_path(path: Path) -> bool:
    resolved = resolved_path(path)
    return DIST.resolve() in resolved.parents or resolved == DIST.resolve()


def needs_wasm_rebuild(path: Path) -> bool:
    resolved = resolved_path(path)

    if resolved in ROOT_WATCH_FILES:
        return True
    return any(
        watch_dir.resolve() in resolved.parents or resolved == watch_dir.resolve()
        for watch_dir in WASM_INPUT_DIRS
    )


def serve(port: int = 8000):
    """Serve dist/ and watch for changes, rebuilding automatically."""
    from watchdog.events import FileSystemEventHandler
    from watchdog.observers import Observer

    build(release=False)

    class RebuildHandler(FileSystemEventHandler):
        def __init__(self):
            self._debounce_timer = None
            self._needs_frontend = False
            self._needs_wasm = False

        def _rebuild(self):
            try:
                build(
                    include_frontend=self._needs_frontend,
                    include_wasm=self._needs_wasm,
                )
            except Exception as e:
                print(f"Build error: {e}")
            finally:
                self._needs_frontend = False
                self._needs_wasm = False

        def on_any_event(self, event):
            if getattr(event, "is_directory", False):
                return

            event_path = resolved_path(Path(event.src_path))
            # Ignore changes in dist/
            if should_ignore_path(event_path):
                return

            if needs_wasm_rebuild(event_path):
                self._needs_wasm = True
            if FRONTEND.resolve() in event_path.parents:
                self._needs_frontend = True

            if self._debounce_timer:
                self._debounce_timer.cancel()
            self._debounce_timer = threading.Timer(0.3, self._rebuild)
            self._debounce_timer.start()

    observer = Observer()
    for watch_dir in [
        CONTENT,
        TEMPLATES,
        STATIC,
        FRONTEND,
        *WASM_INPUT_DIRS,
        WORKSPACE_ROOT,
    ]:
        if watch_dir.exists():
            recursive = watch_dir != WORKSPACE_ROOT
            observer.schedule(RebuildHandler(), str(watch_dir), recursive=recursive)
    observer.start()

    handler = functools.partial(
        http.server.SimpleHTTPRequestHandler, directory=str(DIST)
    )
    server = http.server.HTTPServer(("localhost", port), handler)
    print(f"Serving at http://localhost:{port} (watching for changes)")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nStopping.")
        observer.stop()
    observer.join()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Krypton tour SSG")
    parser.add_argument(
        "command", nargs="?", default="build", choices=["build", "serve"]
    )
    parser.add_argument("--port", type=int, default=8000)
    args = parser.parse_args()

    if args.command == "serve":
        serve(args.port)
    else:
        build(release=True)
