// expect: fail index nonzero-divisor precondition
// `key={…}` is evaluated by JavaScript on every render (`_jsx(T, props, key)`):
// its obligations count on components, on plain elements, and on elements nested
// inside a mapped list item.
import { useState } from "react";
import { idiv, requires, type int } from "vreact/spec";
type Doc = { readonly id: int; readonly title: string };
const docs: readonly Doc[] = [{ id: 1, title: "a" }, { id: 2, title: "b" }];
function half(x: int): int {
  requires(x > 0);
  return idiv(x, 2);
}
type ViewerProps = { readonly title: string };
export function Viewer(props: ViewerProps) {
  return <p>{props.title}</p>;
}
export function App() {
  const [sel, setSel] = useState<int>(0);
  const xs: readonly int[] = [0, 1, 2];
  return (
    <div>
      <button onClick={() => setSel(sel + 1)}>next</button>
      <Viewer key={docs[sel].id} title="doc" />
      <p key={half(sel)}>{sel}</p>
      <ul>
        {xs.map((x) => (
          <li key={x}><span key={idiv(1, x)}>{x}</span></li>
        ))}
      </ul>
    </div>
  );
}
