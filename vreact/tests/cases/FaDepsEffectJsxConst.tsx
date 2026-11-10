// expect: verified FaDepsEffectJsxConst=verified
// An effect may list a JSX const, directly or through a useCallback that lists one: it is a new
// element object at every render, so it is `obj` ("possibly changed": the effect runs after every
// render, as in React). Before, both were refused with "JSX values can only appear inside JSX"
// (at the useCallback's `[el]`, which the useCallback alone was accepted with).
import { useState, useCallback, useEffect } from "react";
import { invariant, type int } from "vreact/spec";

export function FaDepsEffectJsxConst() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  const el = <b>{n}</b>;
  const cb = useCallback(() => setN((p) => (p >= 0 ? p : 0)), [el]);
  useEffect(() => {
    cb();
  }, [cb]);
  useEffect(() => {
    setN((p) => (p > 5 ? 5 : p >= 0 ? p : 0));
  }, [el]);
  return (
    <div>
      {el}
      <button type="button" onClick={() => setN(n + 1)}>{n}</button>
    </div>
  );
}
