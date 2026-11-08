// expect: reject src/RnJsxPragmaMid.tsx:10: `@jsx`: JSX pragmas
// TypeScript reads JSX pragmas only from a file's leading comments, so it ignores the two below
// and checks the JSX against React's; esbuild (Vite) and Babel read them from any comment and
// compile the element to `h("p", null, props.n)` of the classic runtime: formerly VERIFIED, and
// a ReferenceError (h is not defined) when the component renders.
import { type int } from "vreact/spec";

export function RnJsxPragmaMid(props: { readonly n: int }) {
  // @jsxRuntime classic
  // @jsx h
  return <p>{props.n}</p>;
}
