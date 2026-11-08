// expect: reject "allowUmdGlobalAccess" is not supported
// `React` is not imported: TypeScript resolves it to the UMD global of React's types (`export as
// namespace React`), which "allowUmdGlobalAccess" lets a module use; a module bundle defines no
// global React, so rendering App throws a ReferenceError. Formerly VERIFIED (`React.useState` was
// recognised by its declaration in React's types, whatever `React` was bound to).
import { type int, invariant } from "vreact/spec";

export function App() {
  const [n, setN] = React.useState<int>(0);
  invariant(n >= 0);
  return <button onClick={() => setN(n + 1)}>{n}</button>;
}
