// expect: fail non-null
// A component's requires(c) is evaluated at every render, and implies evaluates both arguments:
// rendering <Show sel={null} /> reads `props.sel!.v` on null and throws, although
// implies(props.sel !== null, …) holds. (TypeScript does not narrow through a call's arguments,
// hence the `!`; `props.sel === null || props.sel.v >= 0` is the guarded form.)
import { requires, implies, type int } from "vreact/spec";

type Item = { readonly v: int };

function Show(props: { readonly sel: Item | null }) {
  requires(implies(props.sel !== null, props.sel!.v >= 0));
  return <p>shown</p>;
}

export function App() {
  return <Show sel={null} />;
}
