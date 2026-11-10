// expect: reject is used here (stored, passed or rendered) and mutated afterwards
import { requires, type int } from "vreact/spec";

function Size(props: { readonly m: ReadonlyMap<int, int> }) {
  return <li>{props.m.size}</li>;
}

// the views share `n`, which is mutated before they are rendered
export function C(props: { readonly xs: readonly int[] }) {
  requires(props.xs.length === 1 && props.xs[0] === 5);
  const n = new Map<int, int>();
  const views = props.xs.map((x) => {
    return n;
  });
  n.set(1, 1);
  const first = views[0];
  return <ul><Size m={first} /><li>{first.size === 0 ? "empty" : "full"}</li></ul>;
}
