// expect: verified
// Optional selection, narrowing (`!== null`), early return, a function with requires/ensures.
import { useState } from "react";
import { requires, ensures, invariant, type int } from "vreact/spec";
type Note = { readonly id: int; readonly body: string };

export function clampLen(s: string, n: int): string {
  requires(n >= 0);
  ensures((r) => r.length <= n || r === s);
  if (s.length <= n) return s;
  return s.slice(0, n);
}

export function Notes() {
  const [notes] = useState<readonly Note[]>([]);
  const [sel, setSel] = useState<int | null>(null);
  invariant(sel === null || notes.some((n) => n.id === sel));
  const current = sel === null ? null : notes.find((n) => n.id === sel) ?? null;
  if (current === null) {
    return <p>{notes.length} notes</p>;
  }
  return (
    <div>
      <h1>{clampLen(current.body, 20)}</h1>
      <button onClick={() => setSel(null)}>close</button>
    </div>
  );
}
