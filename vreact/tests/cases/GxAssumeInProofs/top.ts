// expect: status verdict=verified-modulo-trusted one=trusted two=trusted three=trusted four=trusted get=assumes readGet=assumes plain=verified why.one=one_eq_two why.two=five_eq_six why.three=anything why.four=seven_eq_eight errors=none
// A user proof that uses `VReact.assumed` (the axiom behind assume(…)) itself states an
// unproved fact of its own: the items relying on it are TRUSTED and the report names the
// declaration, never "ASSUMES" (relies on the program's assume(…) facts) — here the program's
// only assume(…) is in `get`, and `one` … `four` are false (JS: one(true) = 1, not 2). The use
// is found in the kernel terms, whatever its spelling: the axiom's full name, a renaming
// `open`, an auxiliary definition, a tactic. A user lemma that unfolds a function with an
// assume(…) still relies on the program's assume(…) facts only (`readGet`: ASSUMES).
import { ensures, assume, type int } from "vreact/spec";

export function one(x: boolean): int {
  ensures((r: int) => r === 2);
  return x ? 1 : 1;
}
export function two(x: boolean): int {
  ensures((r: int) => r === 6);
  return x ? 5 : 5;
}
export function three(x: boolean): int {
  ensures((r: int) => r === 4);
  return x ? 3 : 3;
}
export function four(x: boolean): int {
  ensures((r: int) => r === 8);
  return x ? 7 : 7;
}

export function get(xs: readonly int[], i: int): int {
  assume(0 <= i && i < xs.length);
  return xs[i];
}
export function readGet(): int {
  ensures((r: int) => r === 10);
  return get([10, 20], 0);
}
// (no numerals: the bogus lemmas above are simp lemmas, `1 = 2` would rewrite `x + 1`)
export function plain(x: boolean): boolean {
  ensures((r: boolean) => r !== x);
  return !x;
}
