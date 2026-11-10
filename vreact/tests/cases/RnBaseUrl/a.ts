// expect: reject import of "b": VTS modules are imported by their path relative to the importing file
// tsconfig "baseUrl" makes TypeScript resolve the bare specifier "b" to src/b.ts; a bundler
// looks for a package named b instead. Import VTS modules relatively ("./b").
import { type int, ensures } from "vreact/spec";
import { K } from "b";

export function k(): int {
  ensures((r) => r === 7);
  return K;
}
