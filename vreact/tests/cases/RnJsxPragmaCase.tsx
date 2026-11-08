// expect: reject src/RnJsxPragmaCase.tsx:2: `@JSXImportSource`: JSX pragmas
/** @JSXImportSource react */
// TypeScript lower-cases pragma names, so it honours this spelling (it would type the JSX
// against the named library's runtime), while esbuild ignores it: rejected in any letter case.
import { type int } from "vreact/spec";

export function RnJsxPragmaCase(props: { readonly n: int }) {
  return <p>{props.n}</p>;
}
