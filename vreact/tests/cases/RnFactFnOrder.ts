// expect: verified K=verified J=verified succ=verified succOfK=verified
// A module-level assert runs after the declarations above it, and function declarations are
// hoisted: a fact about an @opaque constant may call a function declared below the constant,
// and mention a constant declared after it (formerly an internal Lean error, "Unknown
// identifier": the fact's theorem was emitted right after its constant).
import { type int, ensures, assert } from "vreact/spec";

/** @opaque */
export const K: int = 3;

export const J: int = 10;

function succ(x: int): int {
  ensures((r) => r === x + 1);
  return x + 1;
}

assert(succ(K) === 4);
assert(K < J);

export function succOfK(): int {
  ensures((r) => r === 4);
  return succ(K);
}
