// expect: fail unique-keys
// Keys must be distinct; nothing guarantees distinct titles.
import { useState } from "react";
type Item = { readonly id: number; readonly title: string };
export function DupKeys() {
  const [items] = useState<readonly Item[]>([]);
  return <ul>{items.map((it) => <li key={it.title}>{it.title}</li>)}</ul>;
}
