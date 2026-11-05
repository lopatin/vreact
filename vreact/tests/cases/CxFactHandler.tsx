// expect: status App=assumes Picker=verified
// assume(c) / assert(c) facts in an event handler, a robust handler, an effect, a timer
// callback and a callback passed to a child reach that body's own outcome obligations
// (invariant preservation, robustness, the parent's emit): each body below needs its
// fact for them.  The result relies on the assumptions: ASSUMES.
import { useEffect, useState } from "react";
import { assume, assert, invariant, callbackRequires, type int } from "vreact/spec";

export function Picker(props: { readonly onPick: (i: int) => void }) {
  callbackRequires(props.onPick, (i: int) => i >= 0);
  return <button onClick={() => props.onPick(3)}>pick</button>;
}

export function App() {
  const [n, setN] = useState<int>(0);
  const [sel, setSel] = useState<int>(0);
  invariant(n <= 5 && sel <= 10);
  useEffect(() => {
    const id = setTimeout(() => { assume(n < 5); setN(n + 1); }, 100);
    return () => clearTimeout(id);
  }, [n]);
  useEffect(() => {
    assume(n < 5);
    setN(n + 1);
  }, [n]);
  return (
    <div>
      <button onClick={() => { assume(n < 5); setN(n + 1); }}>a</button>
      <button onClick={() => { if (n < 5) { assert(n + 1 <= 5); setN(n + 1); } }}>b</button>
      <button onClick={() => { assume(n < 5); assert(n + 1 <= 5); setN(n + 1); }}>c</button>
      <p onMouseMove={() => { assume(n < 5); setN(n + 1); }}>move</p>
      <Picker onPick={(i) => { assume(i <= 10); setSel(i); }} />
    </div>
  );
}
