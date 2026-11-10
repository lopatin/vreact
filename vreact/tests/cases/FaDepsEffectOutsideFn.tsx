// expect: verified FaDepsCbOuterFn=verified FaDepsEffectOuter=verified
// An effect may list values declared at the top level of the program (a function, a constant, a
// component): each is created once, when the module is evaluated (top-level variables are
// const), so React never sees it change and it contributes no dependency value (the effect runs
// on mount, as `[]` does; `undefined` likewise). Also through a useCallback that lists one
// (`[inc]`, which the useCallback alone was accepted with). Before, `[bump]` was refused at the
// useCallback's `[inc]` with "functions are not first-class in VTS; call the function instead",
// and `[inc]` in an effect the same way (`[Badge]`: "unknown or unsupported identifier").
import { useState, useCallback, useEffect } from "react";
import { invariant, type int } from "vreact/spec";

function inc(p: int): int {
  return p + 1;
}

type Config = { readonly step: int; readonly xs: readonly int[] };
const CFG: Config = { step: 1, xs: [1, 2] };
const LIMIT: int = 3;

export function Badge(props: { readonly v: int }) {
  return <i>{props.v}</i>;
}

export function FaDepsCbOuterFn() {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  const bump = useCallback(() => setN((p) => (p >= 0 ? inc(p) : 0)), [inc]);
  useEffect(() => {
    bump();
  }, [bump]);
  return <p>{n}</p>;
}

export function FaDepsEffectOuter(props: { readonly step: int }) {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  const add = useCallback(
    () => setN((p) => (p >= 0 ? p + CFG.step + (props.step > 0 ? props.step : 0) : 0)),
    [CFG, CFG.step, CFG.xs.length, LIMIT, Badge, props.step],
  );
  useEffect(() => {
    setN((p) => (p >= 0 ? inc(p) : 0));
  }, [inc, LIMIT, CFG.xs, Badge, undefined]);
  useEffect(() => {
    add();
  }, [add, inc]);
  return <Badge v={n} />;
}
