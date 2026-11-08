// expect: reject import of "vreact/spec": TypeScript resolves it to node_modules/fakespec/index.d.ts only through tsconfig "paths"
// tsconfig "paths" maps "vreact/spec" to another installed declaration file: its `int`, contract
// functions and their types are not vreact's, and the bundler loads the real vreact/spec.
import { type int, ensures } from "vreact/spec";

export function k(): int {
  ensures((r) => r === 7);
  return 7;
}
