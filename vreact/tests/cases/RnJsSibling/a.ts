// expect: reject import of "./lib/b": TypeScript resolves it to src/lib/b.ts, but a bundler, relative to this file, loads src/lib/b.js
// A path without an extension is the first file a bundler finds, and Vite tries .js before .ts:
// with src/lib/b.js next to src/lib/b.ts, TypeScript checks b.ts while b.js runs.
import { type int, ensures } from "vreact/spec";
import { K } from "./lib/b";

export function k(): int {
  ensures((r) => r === 7);
  return K;
}
