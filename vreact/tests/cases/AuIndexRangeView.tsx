// expect: verified
// indexOf/findIndex results stored in state keep `-1 <= sel < length`; a render-level index is
// in range when it is not -1.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";

type Row = { readonly id: int; readonly name: string };

export function Pick() {
  const [items] = useState<readonly string[]>(["a", "b"]);
  const [rows] = useState<readonly Row[]>([]);
  const [sel, setSel] = useState<int>(-1);
  const [at, setAt] = useState<int>(-1);
  invariant(sel >= -1 && sel < items.length);
  invariant(-1 <= at && at < rows.length);
  const k = items.indexOf("b");
  const j = rows.findIndex((r) => r.id === 3);
  return (
    <div>
      <button onClick={() => setSel(items.indexOf("b"))}>b</button>
      <button onClick={() => setSel(k)}>k</button>
      <button onClick={() => setAt(j)}>j</button>
      <button onClick={() => setAt(rows.findIndex((r) => r.id === sel))}>r</button>
      <input onChange={(e) => setSel(items.indexOf(e.target.value))} />
      <span>{k !== -1 ? items[k] : ""}</span>
      <span>{j === -1 ? "" : rows[j].name}</span>
      <span>{k >= 0 && k + 1 < items.length ? items[k + 1] : ""}</span>
    </div>
  );
}
