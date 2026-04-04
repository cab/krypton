const TIMEOUT_MS = 30000;
const LINES_PER_FRAME = 5;

export function createReplClient() {
  let worker = null;
  let nextId = 0;
  const pending = new Map();
  let evalQueue = Promise.resolve();

  function ensureWorker() {
    if (worker) return worker;
    worker = new Worker(new URL("./repl-worker.js", import.meta.url), {
      type: "module",
    });

    worker.onmessage = (event) => {
      const { id, type, ...payload } = event.data;
      if (typeof id !== "number") return;

      const handlers = pending.get(id);
      if (!handlers) return;

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
      handlers.resolve({
        sessionReset: false,
        ...payload,
      });
    };

    worker.onerror = (event) => {
      for (const { reject, timer } of pending.values()) {
        clearTimeout(timer);
        reject(event.error ?? new Error(event.message));
      }
      pending.clear();
    };

    return worker;
  }

  function replEval(input, onLog) {
    // Serialize evals through a queue
    const result = evalQueue.then(() => doEval(input, onLog));
    evalQueue = result.catch(() => {});
    return result;
  }

  function doEval(input, onLog) {
    const w = ensureWorker();
    const id = nextId++;
    w.postMessage({ id, type: "eval", input });
    return new Promise((resolve, reject) => {
      const entry = {
        resolve,
        reject,
        timer: null,
        lines: [],
        flushed: "",
        onLog,
        logRAF: null,
      };
      entry.timer = setTimeout(() => {
        if (entry.logRAF) cancelAnimationFrame(entry.logRAF);
        pending.delete(id);
        // Timeout — kill worker and respawn on next eval
        worker.terminate();
        worker = null;
        resolve({
          ok: false,
          sessionReset: true,
          output: "Execution timed out (30s limit). REPL session was reset.",
          diagnostics: [],
          display: "",
        });
      }, TIMEOUT_MS);
      pending.set(id, entry);
    });
  }

  function reset() {
    if (worker) {
      worker.terminate();
      worker = null;
    }
    // Worker recreated lazily on next eval
  }

  function destroy() {
    if (worker) {
      worker.terminate();
      worker = null;
    }
    pending.clear();
  }

  return { eval: replEval, reset, destroy };
}
