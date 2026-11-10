// expect: reject `items.slice` is a method, not a dependency
// `items.slice` is Array.prototype.slice for every array: React keeps the first value (2), and
// after "shrink" the button "last" sets index = 2 with items = ["a"].
import { useState, useMemo } from "react";
import { invariant, type int } from "vreact/spec";

export function FaDepsArraySlice() {
  const [items, setItems] = useState<readonly string[]>(["a", "b", "c"]);
  const [index, setIndex] = useState<int>(0);
  const last: int = useMemo(() => items.slice(1).length, [items.slice]);
  invariant(0 <= index && index < items.length);
  return (
    <div>
      <p>{items[index]}</p>
      <button type="button" onClick={() => { setItems(["a"]); setIndex(0); }}>shrink</button>
      <button type="button" onClick={() => setIndex(last)}>last</button>
    </div>
  );
}
