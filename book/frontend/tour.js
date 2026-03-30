import { basicSetup, EditorView } from "codemirror";
import { EditorState, Prec } from "@codemirror/state";
import { keymap } from "@codemirror/view";
import { indentUnit } from "@codemirror/language";
import { setDiagnostics, lintGutter } from "@codemirror/lint";

import kryptonTmLanguage from "../../vscode-grammar/krypton.tmLanguage.json";
import { createKryptonLanguage } from "./krypton-language.js";
import { runSnippet } from "./playground-client.js";

const kryptonLanguage = createKryptonLanguage(kryptonTmLanguage);

const kryptonTheme = EditorView.theme({
  "&": {
    backgroundColor: "var(--code-bg)",
    color: "var(--code-fg)",
    fontFamily: "var(--mono)",
    fontSize: "14px",
    borderRadius: "0",
  },
  ".cm-content": {
    padding: "0.6rem 0",
    caretColor: "var(--code-fg)",
  },
  ".cm-scroller": {
    fontFamily: "var(--mono)",
    lineHeight: "1.5",
  },
  ".cm-line": {
    padding: "0 0.75rem",
  },
  ".cm-gutters": {
    backgroundColor: "var(--code-gutter-bg)",
    color: "var(--code-gutter-fg)",
    borderRight: "1px solid var(--code-gutter-border)",
    minWidth: "2.75rem",
  },
  ".cm-lineNumbers .cm-gutterElement": {
    padding: "0 0.65rem 0 0.85rem",
  },
  ".cm-activeLineGutter": {
    backgroundColor: "var(--code-active-line)",
    color: "var(--code-fg)",
  },
  ".cm-activeLine": {
    backgroundColor: "var(--code-active-line)",
  },
  "&.cm-focused": {
    outline: "none",
  },
  "&.cm-focused .cm-selectionBackground, ::selection": {
    backgroundColor: "var(--code-selection)",
  },
  ".cm-cursor, .cm-dropCursor": {
    borderLeftColor: "var(--accent)",
  },
  ".cm-keyword": {
    color: "var(--code-keyword)",
  },
  ".cm-operator": {
    color: "var(--code-operator)",
  },
  ".cm-number, .cm-bool": {
    color: "var(--code-number)",
  },
  ".cm-string": {
    color: "var(--code-string)",
  },
  ".cm-comment": {
    color: "var(--code-comment)",
    fontStyle: "italic",
  },
  ".cm-typeName": {
    color: "var(--code-type)",
  },
  ".cm-function, .cm-function-definition": {
    color: "var(--code-function)",
  },
  ".cm-variableName-special": {
    color: "var(--code-special)",
  },
});

function renderDiagnosticsDom(diagnostics, container) {
  container.innerHTML = "";
  for (const diag of diagnostics) {
    const severity = diag.severity === "Error" ? "error" : "warning";
    const el = document.createElement("div");
    el.className = `diagnostic diagnostic-${severity}`;

    const header = document.createElement("div");
    header.className = "diag-header";

    const sevSpan = document.createElement("span");
    sevSpan.className = "diag-severity";
    sevSpan.textContent = severity;
    header.appendChild(sevSpan);

    if (diag.code) {
      const codeSpan = document.createElement("span");
      codeSpan.className = "diag-code";
      codeSpan.textContent = `[${diag.code}]`;
      header.appendChild(codeSpan);
    }

    header.appendChild(document.createTextNode(`: ${diag.message}`));
    el.appendChild(header);

    if (diag.primary_label) {
      const label = document.createElement("div");
      label.className = "diag-label";
      label.textContent = `  --> ${diag.primary_file}: ${diag.primary_label}`;
      el.appendChild(label);
    }

    for (const sec of diag.secondary_labels ?? []) {
      const label = document.createElement("div");
      label.className = "diag-label";
      label.textContent = `  --> ${sec.filename}: ${sec.message}`;
      el.appendChild(label);
    }

    if (diag.help) {
      const helpEl = document.createElement("div");
      helpEl.className = "diag-help";
      helpEl.textContent = `  help: ${diag.help}`;
      el.appendChild(helpEl);
    }

    if (diag.note) {
      const noteEl = document.createElement("div");
      noteEl.className = "diag-note";
      noteEl.textContent = `  note: ${diag.note}`;
      el.appendChild(noteEl);
    }

    container.appendChild(el);
  }
}

function toCmDiagnostics(diagnostics) {
  return diagnostics
    .filter((d) => d.primary_span)
    .map((d) => ({
      from: d.primary_span[0],
      to: d.primary_span[1],
      severity: d.severity === "Error" ? "error" : "warning",
      message: d.message,
      source: d.code,
    }));
}

document.querySelectorAll(".code-block").forEach((block) => {
  const textarea = block.querySelector(".editor");
  const outputEl = block.querySelector(".output");
  const outputText = block.querySelector(".output-text");
  const runBtn = block.querySelector(".run-btn");

  if (!(textarea instanceof HTMLTextAreaElement)) {
    return;
  }

  const host = document.createElement("div");
  host.className = "editor-host";
  textarea.replaceWith(host);

  let view;
  let isRunning = false;
  const run = async () => {
    if (!outputText || isRunning) {
      return;
    }
    isRunning = true;
    outputEl?.classList.add("visible");
    outputText.textContent = "Running...";
    if (runBtn instanceof HTMLButtonElement) {
      runBtn.disabled = true;
    }
    try {
      const result = await runSnippet(view.state.doc.toString(), (log) => {
        outputText.textContent = log;
        outputText.scrollTop = outputText.scrollHeight;
      });
      const diagnostics = result.diagnostics ?? [];
      if (diagnostics.length > 0) {
        renderDiagnosticsDom(diagnostics, outputText);
        view.dispatch(setDiagnostics(view.state, toCmDiagnostics(diagnostics)));
      } else {
        outputText.textContent = result.output || "(no output)";
        requestAnimationFrame(() => {
          outputText.scrollTop = outputText.scrollHeight;
        });
        view.dispatch(setDiagnostics(view.state, []));
      }
    } catch (error) {
      outputText.textContent =
        error instanceof Error
          ? `${error.name}: ${error.message}`
          : String(error);
      view.dispatch(setDiagnostics(view.state, []));
    } finally {
      isRunning = false;
      if (runBtn instanceof HTMLButtonElement) {
        runBtn.disabled = false;
      }
    }
  };

  view = new EditorView({
    parent: host,
    state: EditorState.create({
      doc: textarea.value,
      extensions: [
        basicSetup,
        EditorState.tabSize.of(2),
        indentUnit.of("  "),
        kryptonLanguage,
        kryptonTheme,
        lintGutter(),
        Prec.highest(keymap.of([
          {
            key: "Mod-Enter",
            run: () => {
              run();
              return true;
            },
          },
        ])),
      ],
    }),
  });

  runBtn?.addEventListener("click", run);
});
