// expect: reject import of "./b.ts": TypeScript resolves it to src/gen/b.ts, but a bundler, relative to this file, finds no such file
// "./b.ts" names src/b.ts, which does not exist; tsconfig "rootDirs" makes TypeScript read
// src/gen/b.ts instead. At run time the import fails (ERR_MODULE_NOT_FOUND). Formerly VERIFIED.
import { type int, ensures } from "vreact/spec";
import { K } from "./b.ts";

export function k(): int {
  ensures((r) => r === 7);
  return K;
}
