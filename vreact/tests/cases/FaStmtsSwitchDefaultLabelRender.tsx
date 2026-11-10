// expect: fail nonzero-divisor C=incomplete H=incomplete
// The labels of a switch's default group in a render (C) and in a handler (H) are evaluated too:
// rendering C, or clicking H's button, throws "idiv by zero" for d = 0 once n !== 0 (formerly
// both VERIFIED).
import { useState } from "react";
import { idiv, type int } from "vreact/spec";
export function C(props: { readonly d: int }) {
  const [n, setN] = useState<int>(0);
  let label = "";
  switch (n) {
    case 0:
      label = "zero";
      break;
    case idiv(100, props.d):
    default:
      label = "other";
      break;
  }
  return <button onClick={() => setN(n + 1)}>{label}</button>;
}
export function H(props: { readonly d: int }) {
  const [n, setN] = useState<int>(0);
  return (
    <button
      onClick={() => {
        switch (n) {
          case 0:
            setN(1);
            break;
          default:
          case idiv(100, props.d):
            setN(0);
            break;
        }
      }}
    >
      {n}
    </button>
  );
}
