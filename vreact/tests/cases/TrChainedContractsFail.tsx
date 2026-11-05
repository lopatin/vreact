// expect: fail child-precondition handler
// The chained conditions are still checked: a parent must establish all of them, and a
// handler must preserve all of them.
import { useState } from "react";
import { requires, invariant, type int } from "vreact/spec";

export function TrHeadF(props: { readonly xs: readonly int[] }) {
  requires(props.xs.length > 0);
  requires(props.xs[0] >= 0);
  const [i, setI] = useState<readonly int[]>([1]);
  invariant(i.length > 0);
  invariant(i[0] >= 1);
  return <button onClick={() => setI([0])}>{props.xs[0]} {i[0]}</button>;
}

export function TrHeadFParent() {
  return <TrHeadF xs={[-3]} />;
}
