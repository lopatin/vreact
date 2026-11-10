import { ensures, implies, forall, hole, type int } from "vreact/spec";

type Item = { readonly v: int };

// JS never calls an ensures lambda, and the prover reads implies(a, b) in it as
// `∀ (h : a), b`: synth's tests must not evaluate b where a fails (xs[0].v of [] throws)
export function plus1(xs: readonly Item[], n: int): int {
  ensures((r: int) => r === n + 1);
  ensures((r: int) => implies(xs.length > 0, xs[0].v === xs[0].v));
  return hole<int>();
}

// nested, and under &&
export function plus2(xs: readonly Item[], n: int): int {
  ensures((r: int) => r === n + 2 && implies(n > 0, implies(xs.length > 1, xs[1].v === xs[1].v)));
  return hole<int>();
}

// in a quantifier body
export function plus3(xs: readonly Item[], n: int): int {
  ensures((r: int) => r === n + 3);
  ensures((r: int) => forall(0, 3, (i) => implies(i < xs.length, xs[i].v === xs[i].v)));
  return hole<int>();
}

// in an every body, with a narrowing antecedent
export function minus1(xs: readonly Item[], o: Item | null, n: int): int {
  ensures((r: int) => r === n - 1);
  ensures((r: int) => xs.every((x) => implies(o !== null, o!.v === o!.v + 0 * x.v)));
  return hole<int>();
}

// under ?:, || and !
export function minus2(xs: readonly Item[], n: int): int {
  ensures((r: int) => r === n - 2);
  ensures((r: int) => n < 0 || (n >= 0 ? !implies(xs.length > 0, xs[0].v !== xs[0].v) || xs.length === 0 : true));
  return hole<int>();
}
