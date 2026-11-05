// expect: fail nonzero-divisor TrJsxUnused=incomplete TrJsxGuardedUse=incomplete TrJsxInMap=incomplete
// JS evaluates a JSX const (its `{…}` children and attributes) at the declaration, whether
// or not, and wherever, it is rendered: its obligations are checked there, unconditionally.
import { useState } from "react";
import { distinct, idiv, invariant, type int } from "vreact/spec";

// never rendered: render still computes idiv(10, 0) once n = 0
export function TrJsxUnused() {
  const [n, setN] = useState<int>(1);
  const row = <p>{idiv(10, n)}</p>;
  return <button onClick={() => setN(0)}>{n}</button>;
}

// rendered only when n > 0, but evaluated on every render
export function TrJsxGuardedUse() {
  const [n, setN] = useState<int>(1);
  const row = <p title={String(idiv(10, n))}>x</p>;
  return n > 0 ? row : <button onClick={() => setN(0)}>{n}</button>;
}

// inside a list item: evaluated for every item, also when the item does not render it
export function TrJsxInMap() {
  const [xs, setXs] = useState<readonly int[]>([1, 2]);
  invariant(distinct(xs));
  return (
    <ul>
      {xs.map((x) => {
        const q = <b>{idiv(10, x)}</b>;
        return <li key={x}>{x > 0 ? q : null}</li>;
      })}
      <li><button onClick={() => setXs([0])}>zero</button></li>
    </ul>
  );
}
