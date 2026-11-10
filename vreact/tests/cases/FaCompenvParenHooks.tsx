// expect: verified C=verified
// Parenthesized hook calls are the same calls in JS: `(useEffect(…))` and
// `const [n, setN] = (useState(0))` are accepted like the plain forms (formerly rejected with
// "hooks must be called at the top level of a component, unconditionally (Rules of Hooks)").
import * as React from "react";
import { invariant, type int } from "vreact/spec";
export function C() {
  const [n, setN] = (React.useState<int>(0));
  const [m, setM] = ((React.useState<int>(1)));
  invariant(n >= 0 && m >= 1);
  (React.useEffect(() => {
    const id = setInterval(() => setN((k) => k + 1), 1000);
    return () => clearInterval(id);
  }, []));
  const twice = (React.useMemo(() => m * 2, [m]));
  return <button onClick={() => setM((k) => k + 1)}>{n} {twice}</button>;
}
