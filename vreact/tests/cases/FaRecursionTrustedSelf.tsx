// expect: status Tree=trusted App=relative
// Positive: a @trusted component's body is not translated (its render is assumed), so it may
// render itself; the check that rejects a self-rendering component skips it.
import { type int } from "vreact/spec";
/** @trusted */
export function Tree(props: { readonly d: int }) {
  return <div>{props.d > 0 ? <Tree d={props.d - 1} /> : null}</div>;
}
export function App() {
  return <Tree d={3} />;
}
