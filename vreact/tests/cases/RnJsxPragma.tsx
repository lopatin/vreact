// expect: reject JSX pragmas (`@jsx`, `@jsxImportSource`, `@jsxFrag`, `@jsxRuntime`) are not supported
/** @jsxImportSource react */
// A comment pragma at the start of a file switches its JSX to another runtime or factory
// (`@jsxImportSource preact`, `@jsx h`); only the configured React runtime is modelled.
import { type int } from "vreact/spec";

export function RnJsxPragma(props: { readonly n: int }) {
  return <p>{props.n}</p>;
}
