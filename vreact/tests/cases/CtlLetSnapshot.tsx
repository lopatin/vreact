// expect: verified
// Closures over `let`s that agree with JS: a closure created after the last assignment, a
// const snapshot taken before a later reassignment, immediate array callbacks (they read
// the current value), and handler-local lets copied before a functional update.
import { useState } from "react";
import { ensures, invariant, type int } from "vreact/spec";

export function ctlSnapshotFn(xs: readonly int[]): int {
  ensures((r: int) => r === 3);
  let x: int = 0;
  x = 3;
  const get = (): int => x;
  let lim: int = 0;
  const none = xs.filter((y) => y < lim && y > lim);
  lim = 1;
  return get() + none.length * 0;
}

export function CtlSnapshot(props: { readonly big: boolean }) {
  const [n, setN] = useState<int>(0);
  invariant(0 <= n && n <= 10);
  let cap: int = 5;
  if (props.big) cap = 10;
  const onSet = () => setN(cap);
  let lim: int = 2;
  const limNow = lim;
  lim = 100;
  return (
    <div>
      <button onClick={onSet}>{n}</button>
      <button onClick={() => setN(limNow)}>{lim}</button>
      <button
        onClick={() => {
          let step: int = 1;
          if (n < 5) step = 2;
          const s = step;
          setN((m) => (m + s <= 10 ? m + s : m));
        }}
      >
        step
      </button>
    </div>
  );
}
