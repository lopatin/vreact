// expect: status five=trusted one=relative Box=trusted App=relative App.certificate=relative
// Of a @trusted declaration only what is translated is closure-checked: its contracts and a
// component's initial state.  Its body, which is not translated, may still use closures over
// reassigned lets (`get`, `show`), and its contracts may use block-bodied callbacks whose
// closures agree with JS (no write after the closure is created).  Callers rely on them.
import { useState } from "react";
import { callbackRequires, ensures, invariant, requires, type int } from "vreact/spec";

/** @trusted */
export function five(xs: readonly int[]): int {
  requires(xs.every((x) => { const y = x; const g = () => y; return g() > 0; }));
  ensures((r: int) => [r].every((x) => { let y = 0; y = x; const g = () => y; return g() === 5; }));
  let k = 1;
  const get = () => k;
  k = 5;
  return get();
}

export function one(): int {
  ensures((r: int) => r === 6);
  return five([1, 2]) + 1;
}

type BP = { readonly onPick: (i: int) => void };

/** @trusted */
export function Box(props: BP) {
  callbackRequires(props.onPick, (i) => {
    const j = i;
    const ok = () => j >= 0;
    return ok();
  });
  const [xs, setXs] = useState<readonly int[]>(() => {
    const a: readonly int[] = [1];
    const f = () => a;
    return f();
  });
  invariant(xs.every((x) => { const g = () => x; return g() > 0; }));
  let label = "a";
  const show = () => label;
  label = "b";
  return (
    <button
      onClick={() => {
        setXs([...xs, 2]);
        props.onPick(xs.length);
      }}
    >
      {show()}
    </button>
  );
}

export function App() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  return <Box onPick={(i) => setN(i)} />;
}
