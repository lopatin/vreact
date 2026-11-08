// expect: verified
// vreact/spec's functions and `int` are recognised by their declaration, also under an import
// alias: `I` is int (formerly `type int as I` silently became number, Lean Float, and this
// contract was not provable), `pre`/`post`/`all` are requires/ensures/forall.
import { requires as pre, ensures as post, forall as all, type int as I } from "vreact/spec";

export function clampIdx(i: I, n: I): I {
  pre(n > 0);
  post((r: I) => r >= 0 && r < n);
  return i < 0 ? 0 : i >= n ? n - 1 : i;
}

export function firstBelow(xs: readonly I[], n: I): boolean {
  pre(xs.length > 0 && all(0, xs.length, (j) => xs[j] < n));
  post((r) => r);
  return xs[0] < n;
}

// a project type spelled `int` is the project's own type (here number)
type int = number;
export function half(x: int): int {
  return x / 2;
}
