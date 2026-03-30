const TIMEOUT_MS = 5000;
const LINES_PER_FRAME = 5;

let nextRequestId = 0;
const pending = new Map();
let worker;

function createWorker() {
  worker = new Worker(new URL("./playground-worker.js", import.meta.url), {
    type: "module",
  });

  worker.onmessage = (event) => {
    const { id, type, ...payload } = event.data;
    if (typeof id !== "number") {
      return;
    }
    const handlers = pending.get(id);
    if (!handlers) {
      return;
    }
    if (type === "log") {
      handlers.lines.push(payload.text);
      if (handlers.onLog && !handlers.logRAF) {
        const pump = () => {
          const batch = handlers.lines.splice(0, LINES_PER_FRAME);
          if (batch.length === 0) {
            handlers.logRAF = null;
            return;
          }
          handlers.flushed += batch.join("");
          handlers.onLog(handlers.flushed);
          handlers.logRAF = requestAnimationFrame(pump);
        };
        handlers.logRAF = requestAnimationFrame(pump);
      }
      return;
    }
    clearTimeout(handlers.timer);
    pending.delete(id);
    handlers.resolve(payload);
  };

  worker.onerror = (event) => {
    for (const { reject, timer } of pending.values()) {
      clearTimeout(timer);
      reject(event.error ?? new Error(event.message));
    }
    pending.clear();
  };
}

createWorker();

export function runSnippet(source, onLog) {
  const id = nextRequestId++;
  worker.postMessage({ id, source });
  return new Promise((resolve, reject) => {
    const entry = { resolve, reject, timer: null, lines: [], flushed: "", onLog };
    entry.timer = setTimeout(() => {
      if (entry.logRAF) cancelAnimationFrame(entry.logRAF);
      pending.delete(id);
      worker.terminate();
      createWorker();
      const allOutput = entry.flushed + entry.lines.join("");
      const sections = [];
      if (allOutput) sections.push(allOutput.trimEnd());
      sections.push("Execution timed out (5s limit)");
      resolve({
        ok: false,
        output: sections.join("\n\n"),
        diagnostics: [],
        warnings: [],
        error: "Execution timed out (5s limit)",
      });
    }, TIMEOUT_MS);
    pending.set(id, entry);
  });
}
