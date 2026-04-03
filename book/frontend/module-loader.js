/** Shared module loader for compiling Krypton JS output into importable data: URLs. */

export function normalizePath(path) {
  return path.replace(/\\/g, "/").replace(/^\.\//, "");
}

export function resolveRelativePath(fromPath, specifier) {
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

export function rewriteModuleSpecifiers(source, filePath, resolveImport) {
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

export function encodeModuleSource(source) {
  const bytes = new TextEncoder().encode(source);
  let binary = "";
  for (const byte of bytes) {
    binary += String.fromCharCode(byte);
  }
  return `data:text/javascript;base64,${btoa(binary)}`;
}

export function createModuleLoader(files) {
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
