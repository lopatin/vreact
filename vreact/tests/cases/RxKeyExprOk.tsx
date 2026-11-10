// expect: verified
// The key-to-reset pattern with a guarded key: obligations in keys are proved.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
type Doc = { readonly id: int; readonly title: string };
const docs: readonly Doc[] = [{ id: 1, title: "a" }, { id: 2, title: "b" }];
type ViewerProps = { readonly title: string };
export function Viewer(props: ViewerProps) {
  return <p>{props.title}</p>;
}
export function App() {
  const [sel, setSel] = useState<int>(0);
  invariant(0 <= sel && sel < docs.length);
  return (
    <div>
      <button onClick={() => { if (sel + 1 < docs.length) setSel(sel + 1); }}>next</button>
      <Viewer key={docs[sel].id} title={docs[sel].title} />
      <p key={"static"}>{sel}</p>
    </div>
  );
}
