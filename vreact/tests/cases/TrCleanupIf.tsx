// expect: verified
// Effect cleanups may use if/else around the allowed calls (pure conditions).
import { useState, useEffect } from "react";
import { invariant, type int } from "vreact/spec";
export function TrTicker(props: { readonly label: string; readonly fast: boolean }) {
  const [n, setN] = useState<int>(0);
  invariant(0 <= n && n <= 10);
  useEffect(() => {
    const id = setInterval(() => setN((m) => (m < 10 ? m + 1 : m)), props.fast ? 100 : 1000);
    return () => {
      if (id !== null) clearInterval(id);
      if (props.label.length > 0) {
        console.log("stop", props.label);
      } else if (n > 5) {
        document.title = "late";
      } else {
        localStorage.setItem("n", String(n));
      }
    };
  }, [props.fast, props.label, n]);
  return <p>{n}</p>;
}
