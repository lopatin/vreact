// expect: verified
// Effect cleanups that only clear timers and make external writes are accepted.
import { useState, useEffect } from "react";
import { invariant, type int } from "vreact/spec";
export function CtlTicker(props: { readonly label: string }) {
  const [n, setN] = useState<int>(0);
  invariant(0 <= n && n <= 10);
  useEffect(() => {
    const id = setInterval(() => setN((m) => (m < 10 ? m + 1 : m)), 1000);
    return () => {
      clearInterval(id);
      console.log("stop", props.label.length);
      document.title = props.label;
      localStorage.setItem("n", String(n));
    };
  }, [props.label, n]);
  return <p>{n}</p>;
}
