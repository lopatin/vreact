// expect: reject src/RnTsExpectError.tsx:9: `@ts-expect-error` is not supported
// Without "allowUmdGlobalAccess" TypeScript rejects the use of React's UMD global in a module
// (TS2686); the suppression comment below silences that error, and the module throws a
// ReferenceError when App renders. All three suppression directives (line-level, expected-error,
// file-level) are rejected; `React.useState` through anything but an import would be, too.
import { type int, invariant } from "vreact/spec";

export function App() {
  // @ts-expect-error
  const [n, setN] = React.useState<int>(0);
  invariant(n >= 0);
  return <button onClick={() => setN(n + 1)}>{n}</button>;
}
