import { mkdirSync, rmSync } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

import { build } from 'esbuild';

const rootDir = path.dirname(fileURLToPath(import.meta.url));
const distDir = path.join(rootDir, 'dist');
const entryPoints = {
  actor: path.join(rootDir, 'src/actor.mts'),
  array: path.join(rootDir, 'src/array.mts'),
  convert: path.join(rootDir, 'src/convert.mts'),
  io: path.join(rootDir, 'src/io.mts'),
  json: path.join(rootDir, 'src/json.mts'),
  map: path.join(rootDir, 'src/map.mts'),
  panic: path.join(rootDir, 'src/panic.mts'),
  prelude: path.join(rootDir, 'src/prelude.mts'),
  'repl-registry': path.join(rootDir, 'src/repl-registry.mts'),
  string: path.join(rootDir, 'src/string.mts'),
};

rmSync(distDir, { recursive: true, force: true });
mkdirSync(distDir, { recursive: true });

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
  });
} catch {
  process.exitCode = 1;
}
