// expect: reject useMemo is missing dependencies: index
// The shorthand property `{ index }` reads `index`: with deps [] React keeps the first value.
import { useState, useMemo } from "react";
import { invariant, type int } from "vreact/spec";
type Sel = { readonly index: int };
export function CtlPickerMemo() {
  const [items, setItems] = useState<readonly string[]>(["a", "b", "c"]);
  const [index, setIndex] = useState<int>(2);
  const [sel, setSel] = useState<Sel>({ index: 0 });
  invariant(0 <= index && index < items.length);
  invariant(0 <= sel.index && sel.index < items.length);
  const pending: Sel = useMemo(() => ({ index }), []);
  return (
    <div>
      <p>{items[sel.index]}</p>
      <button onClick={() => { if (items.length > 1) { setItems(items.slice(1)); setIndex(0); setSel({ index: 0 }); } }}>drop</button>
      <button onClick={() => setSel(pending)}>commit</button>
    </div>
  );
}
