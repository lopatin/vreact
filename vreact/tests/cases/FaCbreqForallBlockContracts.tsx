// expect: verified
// In requires, ensures and invariant too, a forall/exists callback that `(i) => condition` does
// not cover (a block body, a `function (k) { … }`) is read as code instead of being rejected
// ("quantifier body must be an expression"): JS calls it for each i, so that is its meaning.
import { useState } from "react";
import { requires, ensures, invariant, forall, exists, type int } from "vreact/spec";

export function count(n: int): int {
  requires(n >= 0 && forall(0, n, (i) => { return i >= 0; }));
  ensures((r: int) => r === n && exists(0, r + 1, function (k) { return k === 0; }));
  return n;
}

export const THREE: int = count(3);

export function List() {
  const [n, setN] = useState<int>(1);
  invariant(n >= 1 && exists(0, n, (k) => { return k === 0; }));
  return <button onClick={() => setN(n + 1)}>{n}</button>;
}
