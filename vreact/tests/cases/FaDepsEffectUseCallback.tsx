// expect: verified
// An effect that depends on a useCallback function (what react-hooks/exhaustive-deps asks for):
// React returns the cached function until one of its own dependencies changes, so the effect's
// dependency values are those of the function's dependencies (`tick`: none, the effect runs once
// like `[]`; `bump`: props.step). Before, `[tick]` was refused as a function value and `[]` as
// missing `tick`.
import { useState, useEffect, useCallback } from "react";
import { invariant, type int } from "vreact/spec";

export function FaDepsTicker() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  const tick = useCallback(() => setN((p) => p + 1), []);
  useEffect(() => {
    const id = setInterval(tick, 1000);
    return () => clearInterval(id);
  }, [tick]);
  return <button type="button" onClick={() => setN(0)}>{n}</button>;
}

export function FaDepsPoller(props: { readonly step: int; readonly label: string }) {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  const bump = useCallback(() => {
    setN((k) => k + (props.step > 0 ? props.step : 0));
  }, [props.step]);
  // a useCallback over another one (and a setter, which never changes)
  const both = useCallback(() => {
    if (props.label !== "") bump();
  }, [bump, props.label, setN]);
  useEffect(() => {
    bump();
  }, [bump]);
  useEffect(() => {
    both();
  }, [both]);
  return <p>{n}</p>;
}
