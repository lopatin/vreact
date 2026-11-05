// expect: reject useCallback is missing dependencies: index
// `{ index }` reads `index`: with deps [] React keeps the first render's closure (index = 2).
import { useState, useCallback } from "react";
import { invariant, type int } from "vreact/spec";
type Sel = { readonly index: int };
export function CtlPicker() {
  const [items, setItems] = useState<readonly string[]>(["a", "b", "c"]);
  const [index, setIndex] = useState<int>(2);
  const [sel, setSel] = useState<Sel>({ index: 0 });
  invariant(0 <= index && index < items.length);
  invariant(0 <= sel.index && sel.index < items.length);
  const commit = useCallback(() => setSel({ index }), []);
  return (
    <div>
      <p>{items[sel.index]}</p>
      <button onClick={() => { if (items.length > 1) { setItems(items.slice(1)); setIndex(0); setSel({ index: 0 }); } }}>drop</button>
      <button onClick={commit}>commit</button>
    </div>
  );
}
