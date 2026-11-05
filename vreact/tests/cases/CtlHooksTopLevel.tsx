// expect: verified
// useMemo / useCallback at the top level with exhaustive deps (shorthand `{ index }` listed).
import { useState, useMemo, useCallback } from "react";
import { invariant, type int } from "vreact/spec";
type Sel = { readonly index: int };
export function CtlPickerOk() {
  const [items, setItems] = useState<readonly string[]>(["a", "b", "c"]);
  const [index, setIndex] = useState<int>(2);
  const [sel, setSel] = useState<Sel>({ index: 0 });
  const commit = useCallback(() => setSel({ index }), [index]);
  const pending: Sel = useMemo(() => ({ index }), [index]);
  invariant(0 <= index && index < items.length);
  invariant(0 <= sel.index && sel.index < items.length);
  return (
    <div>
      <p>{items[sel.index]}</p>
      <button onClick={() => { if (items.length > 1) { setItems(items.slice(1)); setIndex(0); setSel({ index: 0 }); } }}>drop</button>
      <button onClick={commit}>commit</button>
      <button onClick={() => setSel(pending)}>pending</button>
    </div>
  );
}
