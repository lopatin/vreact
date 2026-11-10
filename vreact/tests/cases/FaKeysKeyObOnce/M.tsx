// expect: fail index verdict=not-verified Key=incomplete Cond=incomplete Const=incomplete failed=3 unchecked=3 errors=none uncheckedwhy=depends~on~`sorry`
// The distinct-keys obligation of keyed siblings (`unique-keys`) is about the keys and the
// conditions that select the children, which are already translated (with their obligations)
// in the children: each failing index is one failure, not one more per use in the keys (a key,
// a `?:` condition, a JSX const rendered next to keyed siblings).  The unique-keys goals contain
// the failed proofs, so they are not checked until the indexes are fixed.
import { type int } from "vreact/spec";
export function Key(props: { readonly xs: readonly string[]; readonly i: int }) {
  return (
    <div>
      <p key={props.xs[props.i]!}>x</p>
      <p key="title">y</p>
    </div>
  );
}
export function Cond(props: { readonly xs: readonly string[]; readonly i: int; readonly s: string }) {
  return (
    <div>
      {props.xs[props.i] === "a" ? <p key="a">x</p> : <p key={props.s}>y</p>}
      <p key="b">z</p>
    </div>
  );
}
export function Const(props: { readonly xs: readonly string[]; readonly i: int }) {
  const row = <li key={props.xs[props.i]!}>r</li>;
  return (
    <ul>
      {row}
      <li key="t">t</li>
    </ul>
  );
}
