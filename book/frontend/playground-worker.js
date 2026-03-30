import initPlayground, { compile_to_js } from "/static/compiler/krypton_playground.js";

let initPromise;

function ensureCompiler() {
  if (!initPromise) {
    initPromise = initPlayground();
  }
  return initPromise;
}

function normalizePath(path) {
  return path.replace(/\\/g, "/").replace(/^\.\//, "");
}

function resolveRelativePath(fromPath, specifier) {
  const fromSegments = normalizePath(fromPath).split("/");
  fromSegments.pop();

  for (const segment of specifier.split("/")) {
    if (!segment || segment === ".") {
      continue;
    }
    if (segment === "..") {
      fromSegments.pop();
      continue;
    }
    fromSegments.push(segment);
  }

  return fromSegments.join("/");
}

function rewriteModuleSpecifiers(source, filePath, resolveImport) {
  return source.replace(
    /(import\s+(?:[^'"]+?\s+from\s+)?|export\s+[^'"]+?\s+from\s+|import\s*\()\s*(['"])([^'"]+)\2/g,
    (match, prefix, quote, specifier) => {
      if (!specifier.startsWith("./") && !specifier.startsWith("../")) {
        return match;
      }
      const resolved = resolveRelativePath(filePath, specifier);
      return `${prefix}${quote}${resolveImport(resolved)}${quote}`;
    },
  );
}

function encodeModuleSource(source) {
  // Use base64 so nested data: imports cannot break quoted module specifiers.
  const bytes = new TextEncoder().encode(source);
  let binary = "";
  for (const byte of bytes) {
    binary += String.fromCharCode(byte);
  }
  return `data:text/javascript;base64,${btoa(binary)}`;
}

function createModuleLoader(files) {
  const fileMap = new Map(
    files.map((file) => [normalizePath(file.path), file.source]),
  );
  const moduleCache = new Map();
  const inProgress = new Set();

  function moduleUrl(path) {
    const normalizedPath = normalizePath(path);
    if (moduleCache.has(normalizedPath)) {
      return moduleCache.get(normalizedPath);
    }
    if (inProgress.has(normalizedPath)) {
      throw new Error(`cyclic JS module graph is not supported in playground loader: ${normalizedPath}`);
    }
    const source = fileMap.get(normalizedPath);
    if (source == null) {
      throw new Error(`missing compiled JS module: ${normalizedPath}`);
    }

    inProgress.add(normalizedPath);
    try {
      const rewritten = rewriteModuleSpecifiers(source, normalizedPath, moduleUrl);
      const url = encodeModuleSource(rewritten);
      moduleCache.set(normalizedPath, url);
      return url;
    } finally {
      inProgress.delete(normalizedPath);
    }
  }

  return { moduleUrl };
}

function formatResultSections(result) {
  const sections = [];
  if (result.log) {
    sections.push(result.log.trimEnd());
  }
  for (const warning of result.warnings ?? []) {
    sections.push(warning.trimEnd());
  }
  if (result.error) {
    sections.push(result.error.trimEnd());
  }
  return sections.filter(Boolean).join("\n\n");
}

self.onmessage = async (event) => {
  const { id, source } = event.data;
  const response = {
    id,
    ok: false,
    output: "",
    diagnostics: [],
    warnings: [],
    error: "",
  };

  const originalLog = console.log;
  let logged = "";
  console.log = (...args) => {
    originalLog(...args);
    logged += `${args.map((arg) => String(arg)).join(" ")}\n`;
  };

  try {
    await ensureCompiler();
    const compiled = compile_to_js(source);
    response.warnings = compiled.warnings ?? [];
    response.diagnostics = compiled.diagnostics ?? [];

    if (!compiled.success) {
      response.error = response.diagnostics
        .map((d) => `${d.severity === "Error" ? "error" : "warning"}[${d.code}]: ${d.message}`)
        .join("\n");
      response.output = formatResultSections({
        warnings: response.warnings,
        error: response.error,
      });
      self.postMessage(response);
      return;
    }

    const loader = createModuleLoader(compiled.files ?? []);
    const module = await import(loader.moduleUrl(compiled.entry_module));
    if (typeof module.main === "function") {
      const actor = await import(loader.moduleUrl("runtime/js/actor.mjs"));
      await actor.runMain(module.main);
    }

    response.ok = true;
    response.output = formatResultSections({
      log: logged,
      warnings: response.warnings,
    });
    self.postMessage(response);
  } catch (error) {
    response.error = error instanceof Error ? `${error.name}: ${error.message}` : String(error);
    response.output = formatResultSections({
      log: logged,
      warnings: response.warnings,
      error: response.error,
    });
    self.postMessage(response);
  } finally {
    console.log = originalLog;
  }
};
