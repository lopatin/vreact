// expect: verified
// JSX consts are checked at their declaration, with the facts that hold there.
import { useState } from "react";
import { distinct, idiv, invariant, type int } from "vreact/spec";

export function TrJsxOk() {
  const [n, setN] = useState<int>(1);
  invariant(n >= 1 && n <= 5);
  const q = <b>{idiv(10, n)}</b>;
  // nested consts, a const used twice, a handler inside a const
  const row = <p>{q}{q}</p>;
  const inc = <button onClick={() => setN(n < 5 ? n + 1 : n)}>+</button>;
  return <div>{row}{inc}{n > 2 ? row : null}</div>;
}

export function TrJsxGuardedDecl() {
  const [n, setN] = useState<int>(0);
  if (n !== 0) {
    const row = <p>{idiv(10, n)}</p>;
    return <div>{row}<button onClick={() => setN(0)}>reset</button></div>;
  }
  return <button onClick={() => setN(1)}>one</button>;
}

export function TrJsxMapOk() {
  const [xs] = useState<readonly int[]>([1, 2]);
  invariant(distinct(xs));
  return (
    <ul>
      {xs.map((x) => {
        const label = <b>{x}</b>;
        return <li key={x}>{label}</li>;
      })}
    </ul>
  );
}
