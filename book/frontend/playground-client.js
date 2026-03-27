const worker = new Worker(new URL("./playground-worker.js", import.meta.url), {
  type: "module",
});

let nextRequestId = 0;
const pending = new Map();

worker.onmessage = (event) => {
  const { id, ...payload } = event.data;
  if (typeof id !== "number") {
    return;
  }
  const handlers = pending.get(id);
  if (!handlers) {
    return;
  }
  pending.delete(id);
  handlers.resolve(payload);
};

worker.onerror = (event) => {
  for (const { reject } of pending.values()) {
    reject(event.error ?? new Error(event.message));
  }
  pending.clear();
};

export function runSnippet(source) {
  const id = nextRequestId++;
  worker.postMessage({ id, source });
  return new Promise((resolve, reject) => {
    pending.set(id, { resolve, reject });
  });
}
