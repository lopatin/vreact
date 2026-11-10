// expect: reject src/A.tsx:8:1: import of "./x#/../limits": "#" in an import path is not supported: TypeScript resolves it to src/limits.ts, but the bundler (Vite) reads everything from the first "?" or "#" ;; src/B.tsx:3:1: import of "./y%2e/../limits": "%" in an import path is not supported: TypeScript resolves it to src/limits.ts, but the bundler's dev server (vite)
// The checks of the characters a bundler reads as URL syntax in an import path itself (not
// only in a source's file name): TypeScript reads "./x#/../limits" as "./limits"; so would Vite
// here (it normalises the path before cutting it at "#"), but which file a path with such
// characters loads is not something VTS models.
import { useState } from "react";
import { type int, invariant } from "vreact/spec";
import { LIMIT } from "./x#/../limits";
import { STEP } from "./B";

export function A() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0 && n <= 3);
  return <button type="button" onClick={() => { if (n < LIMIT) setN(n + STEP); }}>{n}</button>;
}
