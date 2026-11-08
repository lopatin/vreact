// expect: reject a line break inside a JSX attribute string
// Babel joins the lines of a JSX attribute string with a space, TypeScript keeps them: the
// child would see a different label depending on the compiler.
import { requires } from "vreact/spec";
function Label(props: { readonly text: string }) {
  requires(props.text.length === 4);
  return <p>{props.text}</p>;
}
export function RjAttrLineBreak() {
  return <Label text="a
 b" />;
}
