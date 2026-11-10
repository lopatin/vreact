// expect: reject the props object is not an effect dependency: list the fields the effect reads
// `[props]` in an effect (directly, or through a useCallback that lists it): rejected with a reason
// about dependencies (before: "the props object can only be used through its fields").
import { useState, useEffect, useCallback } from "react";
import { invariant, type int } from "vreact/spec";

type Item = { readonly count: int };
export function FaDepsEffectPropsObject(props: { readonly item?: Item }) {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  const reset = useCallback(() => setN(props.item?.count === 0 ? 0 : 1), [props]);
  useEffect(() => {
    const c = props.item?.count;
    if (c !== undefined && c > 0) setN(c);
  }, [props]);
  useEffect(() => {
    reset();
  }, [reset]);
  return <p>{n}</p>;
}
