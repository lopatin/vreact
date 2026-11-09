// expect: reject is used here (stored, passed or rendered) and mutated afterwards
import { useMemo } from "react";
import { type int } from "vreact/spec";

// useMemo's callback returns `n` itself; the component mutates `n` afterwards
export function C(props: { readonly k: int }) {
  const n = new Map<int, int>();
  const s = useMemo(() => {
    return n;
  }, []);
  n.set(props.k, 1);
  return <p>{s.size === 0 ? "empty" : "full"}</p>;
}
