// expect: verified
// The advice of FaDepsLibConstantMsg / FaDepsOutsideMethodMsg / FaDepsTupleLengthMsg followed:
// values from outside the component (`Math.max`, the top-level `LIMIT`) are left out, and the
// tuple is listed instead of its `length`.
import { useState, useMemo } from "react";
import { invariant, type int } from "vreact/spec";

const LIMIT: int = 5;

type P = { pair: readonly [int, string] };

export function FaDepsOutsideValueOk(props: P) {
  const [n, setN] = useState<int>(0);
  const k: int = useMemo(() => Math.max(n, LIMIT) + (props.pair[0] > 0 ? props.pair[0] : 0), [n, props.pair]);
  invariant(n >= 0);
  return <button type="button" onClick={() => setN(k)}>{n}</button>;
}
