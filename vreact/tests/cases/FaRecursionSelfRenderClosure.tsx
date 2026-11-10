// expect: reject <Tree> inside Tree: a component that refers to itself
// The self-reference in a local helper (a useCallback arrow): every reference of a component
// to itself is rejected as recursion, wherever it is (before: "JSX is only allowed in the value
// returned by a component").
import { useCallback } from "react";
import { type int } from "vreact/spec";
export function Tree(props: { readonly d: int }) {
  const mk = useCallback((n: int) => <Tree d={n} />, []);
  return <div>{props.d > 0 ? mk(props.d - 1) : null}</div>;
}
