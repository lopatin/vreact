// expect: verified has=verified
// Formerly GxRejectSetTypeParam: a Set built in a generic body from elements of an
// equality-constrained type parameter (Lean `JSSet K` with `[DecidableEq K]`).
import { ensures, type int } from "vreact/spec";

export function has<K extends int | string>(xs: readonly K[], k: K): boolean {
  ensures((r: boolean) => r === xs.includes(k));
  const s = new Set<K>(xs);
  return s.has(k);
}
