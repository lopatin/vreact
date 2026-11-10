// expect: fail handler
// False controls for the counting facts of a delete by key: without distinct ids, filtering out
// the selected element's id may remove every element ([{id: 0}, {id: 0}]).
import { useState } from "react";
import { invariant, type int } from "vreact/spec";

type Item = { readonly id: int; readonly name: string };

export function NoDistinct() {
  const [items, setItems] = useState<readonly Item[]>([{ id: 0, name: "a" }]);
  const [sel, setSel] = useState<int>(0);
  invariant(items.length > 0 && 0 <= sel && sel < items.length);
  return (
    <button
      onClick={() => {
        if (items.length <= 1) return;
        setItems(items.filter((i) => i.id !== items[sel].id));
        setSel(0);
      }}
    >
      del
    </button>
  );
}
