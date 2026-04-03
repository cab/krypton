import initPlayground, { compile_to_js } from "/static/compiler/krypton_playground.js";
import { createModuleLoader } from "./module-loader.js";

let initPromise;

function ensureCompiler() {
  if (!initPromise) {
    initPromise = initPlayground();
  }
  return initPromise;
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
    const line = `${args.map((arg) => String(arg)).join(" ")}\n`;
    logged += line;
    self.postMessage({ id, type: "log", text: line });
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
      const actor = await import(loader.moduleUrl("extern/js/actor.mjs"));
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
