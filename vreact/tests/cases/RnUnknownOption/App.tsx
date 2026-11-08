// expect: reject tsconfig: the compiler option "jsxFactory" is not supported by VTS
// Compiler options are a whitelist: an option VTS does not know to leave TypeScript's checks and
// the meaning of the program unchanged is rejected (here the factory of the classic JSX
// runtime, which a bundler reading this tsconfig may use).
import { type int } from "vreact/spec";

export function App(props: { readonly n: int }) {
  return <p>{props.n}</p>;
}
