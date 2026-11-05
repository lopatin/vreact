// expect: verified
// switch on member-access discriminants: an enum prop (`props.mode`), the event's
// `e.key`, a union field of state (`st.shape.kind`) and of props (`props.shape.kind`),
// and destructured props (enum and union), in handlers and in the render.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
type Mode = "inc" | "reset" | "dec";
type Shape = { kind: "circle"; r: int } | { kind: "square"; side: int };
type St = { shape: Shape; total: int };
export function App(props: { readonly mode: Mode; readonly shape: Shape }) {
  const [n, setN] = useState<int>(0);
  const [st, setSt] = useState<St>({ shape: { kind: "circle", r: 1 }, total: 0 });
  invariant(0 <= n && n <= 10 && st.total >= 0);
  return (
    <div>
      <button onClick={() => {
        switch (props.mode) {
          case "inc":
            if (n < 10) setN(n + 1);
            break;
          case "dec":
            if (n > 0) setN(n - 1);
            break;
          default:
            setN(0);
            break;
        }
      }}>{n}</button>
      <input onKeyDown={(e) => {
        switch (e.key) {
          case "Enter":
            setN(0);
            break;
          case "ArrowUp":
            if (n < 10) setN(n + 1);
            break;
        }
      }} />
      <button onClick={() => {
        switch (st.shape.kind) {
          case "circle":
            if (st.shape.r >= 0) setSt({ ...st, total: st.total + st.shape.r });
            break;
          case "square":
            if (st.shape.side >= 0) setSt({ ...st, total: st.total + st.shape.side });
            break;
        }
      }}>shape</button>
      <button onClick={() => {
        switch (props.shape.kind) {
          case "circle":
            if (props.shape.r >= 0) setSt({ ...st, total: st.total + props.shape.r });
            break;
          default:
            break;
        }
      }}>prop shape</button>
    </div>
  );
}
export function Destr({ mode, shape }: { readonly mode: Mode; readonly shape: Shape }) {
  const [n, setN] = useState<int>(0);
  invariant(0 <= n && n <= 10);
  let size: int = 0;
  switch (shape.kind) {
    case "circle":
      size = shape.r;
      break;
    case "square":
      size = shape.side;
      break;
  }
  let sign: string = "";
  switch (mode) {
    case "inc":
      sign = "+";
      break;
    case "dec":
      sign = "-";
      break;
  }
  return (
    <button onClick={() => {
      switch (mode) {
        case "inc":
          if (n < 10) setN(n + 1);
          break;
        default:
          setN(0);
          break;
      }
    }}>{sign}{n} ({size})</button>
  );
}
