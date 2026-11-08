// expect: reject import of "react": it resolves to src/react.ts, not to the installed React package's declarations
// tsconfig "paths" makes TypeScript resolve "react" to the VTS module src/react.ts; the bundler
// (like Node) ignores "paths" and loads the installed React, whose version is "18.3.1": v() is 6
// at run time. Formerly VERIFIED (the VTS module was taken for the import).
import { type int, ensures } from "vreact/spec";
import { version } from "react";

export function v(): int {
  ensures((r) => r === 8);
  return version.length;
}
