// expect: reject effect cleanups may not call `props.onDone`
// A callback hidden inside the argument of an allowed external write is still a call.
import { useEffect } from "react";
type P = { readonly onDone: () => void };
export function CtlNested(props: P) {
  useEffect(() => {
    return () => console.log(props.onDone());
  });
  return <span>x</span>;
}
