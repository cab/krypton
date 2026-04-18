import { mkdirSync, rmSync } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

import { build } from 'esbuild';

const rootDir = path.dirname(fileURLToPath(import.meta.url));
const distDir = path.join(rootDir, 'dist');
const entryPoints = {
  actor: path.join(rootDir, 'src/actor.mts'),
  array: path.join(rootDir, 'src/array.mts'),
  'array-builder': path.join(rootDir, 'src/array-builder.mts'),
  convert: path.join(rootDir, 'src/convert.mts'),
  io: path.join(rootDir, 'src/io.mts'),
  json: path.join(rootDir, 'src/json.mts'),
  map: path.join(rootDir, 'src/map.mts'),
  'map-builder': path.join(rootDir, 'src/map-builder.mts'),
  'map-hashed-key': path.join(rootDir, 'src/map-hashed-key.mts'),
  panic: path.join(rootDir, 'src/panic.mts'),
  prelude: path.join(rootDir, 'src/prelude.mts'),
  'repl-registry': path.join(rootDir, 'src/repl-registry.mts'),
  string: path.join(rootDir, 'src/string.mts'),
};

rmSync(distDir, { recursive: true, force: true });
mkdirSync(distDir, { recursive: true });

const entryBasenames = new Set(Object.keys(entryPoints));
const externalSiblingEntries = {
  name: 'external-sibling-entries',
  setup(build) {
    build.onResolve({ filter: /^\.\/.+\.mjs$/ }, (args) => {
      const base = path.basename(args.path, '.mjs');
      if (entryBasenames.has(base)) {
        return { path: args.path, external: true };
      }
      return null;
    });
  },
};

try {
  await build({
    entryPoints,
    outdir: distDir,
    bundle: true,
    format: 'esm',
    target: 'es2022',
    platform: 'browser',
    splitting: false,
    packages: 'bundle',
    outExtension: { '.js': '.mjs' },
    plugins: [externalSiblingEntries],
  });
} catch {
  process.exitCode = 1;
}
