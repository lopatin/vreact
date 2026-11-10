// expect: status verdict=not-verified one=incomplete two=incomplete three=incomplete four=incomplete get=assumes readGet=incomplete plain=incomplete errors=proof proved=1 unchecked=6 why.one=kernel~re-check why.four=VReact.assumed
// A user proof that uses `VReact.assumed` (the axiom behind assume(…)) itself states an
// unproved fact of its own, never one of the program's assume(…) facts — here the program's
// only assume(…) is in `get`, and `one` … `four` are false (JS: one(true) = 1, not 2). The uses
// are the axiom's full name, a renaming `open`, an auxiliary definition and a tactic.
// Three lines of defence: the proof whitelist rejects the identifier `assumed` (and the tactic
// `vreact_assume`) in proof files (RejectRlAssumed, GxRejectProofAssumeTactic), so the file
// is smuggled/top.lean, put in place after the translation; the kernel re-check then finds
// declarations of Proofs.top that use the axiom directly, and VTS.top.Posts, which imports it,
// is not certified: no obligation there counts (the items are INCOMPLETE, NOT VERIFIED);
// `#vreact_assumed` (the report's audit of the axiom's uses, tests/honesty.ts) would make them
// TRUSTED, naming the declaration, if a use got past both. (Before the merge with the proof
// whitelist and the kernel re-check this case expected one … four TRUSTED, errors=none.)
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
