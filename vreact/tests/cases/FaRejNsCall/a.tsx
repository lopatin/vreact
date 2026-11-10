// expect: verified
// A namespace import of a verified module (`import * as L`): `L.inc(x)` calls lib's inc and
// `L.K` reads lib's constant, exactly as `import { inc, K }` would (formerly rejected as
// "unknown or unsupported identifier `L`"). Also a generic function, a function with a
// precondition, a constant in an effect's cleanup and as a dependency, and a type `L.Item`
// next to a local type of the same name.
import { useEffect, useState } from "react";
import { type int, ensures, requires, invariant } from "vreact/spec";
import * as L from "./lib";

type Item = { readonly id: int; readonly label: string };

export function g(it: L.Item, other: Item): int {
  ensures((r) => r === it.id + 1 + L.K);
  return L.inc(it.id) + (other.label === "" ? L.K : L.K);
}

export function h(xs: readonly int[]): int {
  requires(xs.length > 0);
  ensures((r) => r === xs[0]);
  return L.first(xs);
}

export function k(): boolean {
  ensures((r) => r);
  return L.same<int>(L.K, 3);
}

export function C() {
  const [n, setN] = useState<int>(L.K);
  invariant(n >= L.K);
  useEffect(() => {
    const id = setTimeout(() => setN((m) => L.inc(m)), L.K);
    return () => {
      if (L.K > 0) clearTimeout(id);
      console.log(L.inc(L.K));
    };
  }, [L.K]);
  return <button onClick={() => setN(L.inc(n))}>{n + L.K}</button>;
}
