// expect: verified
// A props path read with `?.` in an effect / useMemo / useCallback is covered by its prefix
// (`[props.item]`) or by the same path (`[props.item?.count]`): an optional link reads the same
// property. Before, no dependency array was accepted for it.
import { useState, useEffect, useMemo, useCallback } from "react";
import { invariant, type int } from "vreact/spec";

type Item = { readonly count: int };

export function FaDepsBadge(props: { readonly item?: Item }) {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  useEffect(() => {
    const c = props.item?.count;
    if (c !== undefined && c > 0) setN(c);
  }, [props.item]);
  useEffect(() => {
    const c = props.item?.count;
    if (c !== undefined && c > 0) setN(c);
  }, [props.item?.count]);
  const reset = useCallback(() => {
    const c = props.item?.count;
    setN(c !== undefined && c > 0 ? c : 0);
  }, [props.item?.count]);
  return <button type="button" onClick={reset}>{n}</button>;
}

export function FaDepsLabel(props: { readonly item?: Item }) {
  const c: int = useMemo(() => props.item?.count ?? 0, [props.item]);
  const d: int = useMemo(() => props.item?.count ?? 0, [props.item?.count]);
  return <p>{c + d}</p>;
}
