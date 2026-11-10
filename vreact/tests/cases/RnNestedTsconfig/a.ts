// expect: reject lib/tsconfig.json is not supported: the bundler compiles src/lib/b.tsx with the settings of the tsconfig.json nearest to it
// Vite's esbuild compiles each file with the tsconfig.json nearest to it; the one in lib/ makes
// JSX preact's there, while VTS checks every source with the project's tsconfig.json (React).
import { type int, ensures } from "vreact/spec";

export function f(x: int): int {
  ensures((r) => r === x);
  return x;
}
