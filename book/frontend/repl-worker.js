import initPlayground, {
  repl_create,
  repl_eval,
  repl_commit,
  repl_reset,
  repl_destroy,
} from "/static/compiler/krypton_playground.js";
import { createModuleLoader, normalizePath, encodeModuleSource, rewriteModuleSpecifiers } from "./module-loader.js";

let initPromise;
function ensureCompiler() {
  if (!initPromise) {
    initPromise = initPlayground();
  }
  return initPromise;
}

let sessionId = null;
let runtimeUrls = null; // Map<path, dataUrl> — loaded once, shared across evals

function buildRuntimeUrls(runtimeFiles) {
  const map = new Map();
  const loader = createModuleLoader(runtimeFiles);
  for (const file of runtimeFiles) {
    const path = normalizePath(file.path);
    map.set(path, loader.moduleUrl(path));
  }
  return map;
}

function buildEvalLoader(evalFiles) {
  // Merge eval files with cached runtime URLs
  const fileMap = new Map(
    evalFiles.map((f) => [normalizePath(f.path), f.source]),
  );
  const moduleCache = new Map();
  const inProgress = new Set();

  function moduleUrl(path) {
    const np = normalizePath(path);
    if (moduleCache.has(np)) return moduleCache.get(np);
    // Check runtime cache first
    if (runtimeUrls && runtimeUrls.has(np)) return runtimeUrls.get(np);
    if (inProgress.has(np)) {
      throw new Error(`cyclic JS module graph: ${np}`);
    }
    const source = fileMap.get(np);
    if (source == null) {
      throw new Error(`missing compiled JS module: ${np}`);
    }
    inProgress.add(np);
    try {
      const rewritten = rewriteModuleSpecifiers(source, np, moduleUrl);
      const url = encodeModuleSource(rewritten);
      moduleCache.set(np, url);
      return url;
    } finally {
      inProgress.delete(np);
    }
  }

  return { moduleUrl };
}

function formatValue(v) {
  if (v === undefined || v === null) return "()";
  if (typeof v === "string") return JSON.stringify(v);
  if (typeof v === "number" || typeof v === "boolean") return String(v);
  return String(v);
}

self.onmessage = async (event) => {
  const { id, type: msgType, input } = event.data;

  if (msgType === "reset") {
    if (sessionId != null) {
      try { repl_reset(sessionId); } catch (_) { /* ignore */ }
    }
    runtimeUrls = null;
    self.postMessage({ id, type: "reset-done" });
    return;
  }

  if (msgType !== "eval") return;

  const originalLog = console.log;
  let logged = "";
  console.log = (...args) => {
    const line = `${args.map((a) => String(a)).join(" ")}\n`;
    logged += line;
    self.postMessage({ id, type: "log", text: line });
  };

  try {
    await ensureCompiler();
    if (sessionId == null) {
      sessionId = repl_create();
    }

    const result = repl_eval(sessionId, input);

    if (!result.success) {
      self.postMessage({
        id,
        type: "result",
        ok: false,
        diagnostics: result.diagnostics ?? [],
        display: "",
        output: "",
      });
      console.log = originalLog;
      return;
    }

    // On first eval, cache runtime URLs
    if (result.include_runtime && result.runtime_files?.length > 0) {
      runtimeUrls = buildRuntimeUrls(result.runtime_files);
    }

    // Build loader and execute
    const loader = buildEvalLoader(result.files ?? []);
    const mod = await import(loader.moduleUrl(result.entry_module));
    const value = await mod.__repl_eval();

    // Execution succeeded — commit state
    repl_commit(sessionId);

    // Format output
    let output = "";
    if (result.display) {
      // let binding ("x: Int") or fun def ("f: (Int) -> Int")
      output = result.display;
    } else {
      // bare expr — just show the value
      output = formatValue(value);
    }

    if (logged) {
      output = logged.trimEnd() + "\n" + output;
    }

    self.postMessage({
      id,
      type: "result",
      ok: true,
      display: result.display,
      output,
      diagnostics: [],
    });
  } catch (error) {
    // Do NOT commit on error
    const message = error instanceof Error ? `${error.name}: ${error.message}` : String(error);
    self.postMessage({
      id,
      type: "result",
      ok: false,
      display: "",
      output: message,
      diagnostics: [],
    });
  } finally {
    console.log = originalLog;
  }
};
