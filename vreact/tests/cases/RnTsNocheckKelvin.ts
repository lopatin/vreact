// expect: reject src/RnTsNocheckKelvin.ts:2: `@ts-nochecK` is not supported
// @ts-nochecK
// The last letter above is U+212A KELVIN SIGN, which JavaScript's toLowerCase maps to "k":
// TypeScript lower-cases pragma names, so this is the file-wide suppression too.
import { type int, ensures } from "vreact/spec";

export function f(): int {
  ensures((r) => r === 1);
  const x: int | undefined = null;
  return x === undefined ? 1 : 2;
}
