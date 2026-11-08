// expect: reject a character reference to a line break inside a JSX attribute string
// "a&#10; b" is "a\n b" (4 characters) in TypeScript's and esbuild's JSX transforms, but
// Babel's replaces the decoded line break and the space after it with one space ("a b"): the
// child's precondition would depend on the compiler, as for a raw line break.
import { requires } from "vreact/spec";
function Label(props: { readonly text: string }) {
  requires(props.text.length === 4);
  return <p>{props.text}</p>;
}
export function RjAttrNewlineRef() {
  return <Label text="a&#10; b" />;
}
