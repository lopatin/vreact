// expect: reject parent callbacks cannot be invoked
// onBlur is robust: focus moves inside other batches (a label click focusing its control,
// autoFocus during a commit), so a blur handler may share a batch with another
// component's handler; two parent callbacks from one snapshot would not compose.
import { useState } from "react";
export function Field(props: { readonly onCommit: (v: string) => void }) {
  const [v, setV] = useState<string>("");
  return <input value={v} onChange={(e) => setV(e.target.value)} onBlur={() => props.onCommit(v)} />;
}
