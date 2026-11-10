// expect: verified Ticker=verified Capped=verified Closure=verified
// A timer callback reads the consts of its effect body declared before the registration
// (formerly rejected: "unknown or unsupported identifier `step`"). It is translated in the
// effect body's environment at the registration: each const is bound to its value (computed
// from the snapshot), and a guard that reads one is used too (`Capped`). `Closure`: the
// callback is an effect-local arrow function.
import { useState, useEffect } from "react";
import { invariant, type int } from "vreact/spec";

export function Ticker(props: { readonly fast: boolean }) {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  useEffect(() => {
    const step: int = props.fast ? 2 : 1;
    const id = setInterval(() => setN((k) => k + step), 100);
    return () => clearInterval(id);
  }, [props.fast]);
  return <p>{n}</p>;
}

export function Capped(props: { readonly max: int }) {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0 && n <= 100);
  useEffect(() => {
    const limit: int = props.max > 100 ? 100 : props.max;
    if (n >= limit) return;
    const id = setTimeout(() => setN(n + 1), 100);
    return () => clearTimeout(id);
  }, [n, props.max]);
  return <p>{n}</p>;
}

export function Closure() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  useEffect(() => {
    const tick = () => setN((k) => k + step);
    const step: int = 3;
    const id = setInterval(tick, 100);
    return () => clearInterval(id);
  }, []);
  return <p>{n}</p>;
}
