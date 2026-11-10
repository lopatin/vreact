// expect: verified plus1=verified plus2=verified plus3=verified minus1=verified minus2=verified
// The filled tests/synth/fixtures/FaImpliesSynthEnsures: in an ensures lambda (never called)
// implies(a, b) reads b under a in every position vreact synth's tests evaluate as `!a || b`
// (the body, nested implies, &&, ||, !, ?:, forall and every bodies, a narrowing antecedent).
import { ensures, implies, forall, type int } from "vreact/spec";

type Item = { readonly v: int };

export function plus1(xs: readonly Item[], n: int): int {
  ensures((r: int) => r === n + 1);
  ensures((r: int) => implies(xs.length > 0, xs[0].v === xs[0].v));
  return n + 1;
}

export function plus2(xs: readonly Item[], n: int): int {
  ensures((r: int) => r === n + 2 && implies(n > 0, implies(xs.length > 1, xs[1].v === xs[1].v)));
  return n + 2;
}

export function plus3(xs: readonly Item[], n: int): int {
  ensures((r: int) => r === n + 3);
  ensures((r: int) => forall(0, 3, (i) => implies(i < xs.length, xs[i].v === xs[i].v)));
  return n + 3;
}

export function minus1(xs: readonly Item[], o: Item | null, n: int): int {
  ensures((r: int) => r === n - 1);
  ensures((r: int) => xs.every((x) => implies(o !== null, o!.v === o!.v + 0 * x.v)));
  return n - 1;
}

export function minus2(xs: readonly Item[], n: int): int {
  ensures((r: int) => r === n - 2);
  ensures((r: int) => n < 0 || (n >= 0 ? !implies(xs.length > 0, xs[0].v !== xs[0].v) || xs.length === 0 : true));
  return n - 2;
}
