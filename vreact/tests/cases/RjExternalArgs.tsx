// expect: fail index nonzero-divisor non-null precondition RjExtHandler=incomplete RjExtEffect=incomplete RjExtCleanup=incomplete RjExtTimer=incomplete RjExtDelay=incomplete RjExtRender=incomplete RjExtGuarded=verified
// The arguments of external writes (console.*, localStorage.setItem, document.title = …)
// and a timer's delay are evaluated by JS — they may throw (`xs[9].name`, `x!.f`), divide by
// zero in `idiv` (which throws), or call a function outside its precondition — so they are
// translated with their obligations wherever they appear: handlers, effects, cleanups,
// timer callbacks, render. Their values have no modelled effect.
import { useState, useEffect } from "react";
import { invariant, requires, idiv, type int } from "vreact/spec";

type R = { readonly name: string };

export function half(x: int): int {
  requires(x > 0);
  return idiv(x, 2);
}

export function RjExtHandler(props: { readonly recs: readonly R[] }) {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  return <button type="button" onClick={() => { console.log(props.recs[9].name); setN(n + 1); }}>{n}</button>;
}

export function RjExtEffect() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  useEffect(() => {
    document.title = String(idiv(100, n));
  }, [n]);
  return <button type="button" onClick={() => setN(n + 1)}>{n}</button>;
}

export function RjExtCleanup(props: { readonly label: R | null }) {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  const label = props.label;
  useEffect(() => {
    return () => localStorage.setItem("k", label!.name);
  }, [label]);
  return <button type="button" onClick={() => setN(n + 1)}>{n}</button>;
}

export function RjExtTimer() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  useEffect(() => {
    const id = setTimeout(() => console.log(half(n)), 100);
    return () => clearTimeout(id);
  }, [n]);
  return <button type="button" onClick={() => setN(n + 1)}>{n}</button>;
}

export function RjExtDelay() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  useEffect(() => {
    const id = setTimeout(() => setN((m) => m + 1), idiv(1000, n));
    return () => clearTimeout(id);
  }, [n]);
  return <p>{n}</p>;
}

export function RjExtRender(props: { readonly recs: readonly R[] }) {
  console.log(props.recs[0].name);
  return <p>{props.recs.length}</p>;
}

// guarded: the same writes are safe under the conditions where they run (an early return
// of the effect body also guards its cleanup; a timer handle is never null)
export function RjExtGuarded(props: { readonly recs: readonly R[]; readonly i: int }) {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  useEffect(() => {
    if (props.i < 0 || props.i >= props.recs.length) return;
    console.log("rec", props.recs[props.i].name);
    document.title = props.recs[props.i].name;
    const id = setTimeout(() => { if (n > 0) console.log(half(n)); }, idiv(1000, n + 1));
    return () => {
      if (id !== null) clearTimeout(id);
      localStorage.setItem("k", props.recs[props.i].name);
    };
  }, [props.i, props.recs, n]);
  return (
    <button type="button" onClick={() => { if (props.recs.length > 0) console.log(props.recs[0].name); setN(n + 1); }}>
      {n}
    </button>
  );
}
