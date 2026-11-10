// expect: verified
// Data paths that stay accepted: a Map / array / record listed whole covers its method calls
// (`m.has(k)`, `item.tags.includes(…)`), `size` and `length` and record fields are dependencies
// of their own reads.
import { useState, useMemo, useCallback } from "react";
import { invariant, type int } from "vreact/spec";

type Item = { readonly count: int; readonly tags: readonly string[] };

export function FaDepsDataPathsOk(props: { readonly m: ReadonlyMap<int, string>; readonly onPick: (x: int) => void }) {
  const [m, setM] = useState<ReadonlyMap<int, string>>(new Map<int, string>([[1, "a"]]));
  const [xs, setXs] = useState<readonly string[]>(["a"]);
  const [item, setItem] = useState<Item>({ count: 0, tags: [] });
  const [sel, setSel] = useState<int>(1);
  invariant(sel >= 1);
  const pick: int = useMemo(() => (m.has(2) ? 2 : 1), [m]);
  const size: int = useMemo(() => m.size + props.m.size, [m.size, props.m.size]);
  const len: int = useMemo(() => xs.length, [xs.length]);
  const tagged: int = useMemo(() => item.count + (item.tags.includes("x") ? 1 : 0), [item.count, item.tags]);
  const choose = useCallback(() => props.onPick(props.m.has(2) ? 2 : 1), [props.onPick, props.m]);
  return (
    <div>
      <p>{size + len + tagged}</p>
      <button type="button" onClick={() => { setM(new Map<int, string>()); setXs([]); setItem({ count: 1, tags: ["x"] }); }}>change</button>
      <button type="button" onClick={() => setSel(pick)}>select</button>
      <button type="button" onClick={choose}>choose</button>
    </div>
  );
}
