// expect: verified
import { useEffect, useState } from "react";
import { invariant, type int } from "vreact/spec";

// Timer delays and cleanups (data only; also translated, with their obligations, so every call
// must be one VTS models) may use the library's reading methods: array, string and number
// methods, Math.*, JSON.stringify, Map/Set reads, inline callbacks.  (Merge with r4-jsx, which
// translates cleanup arguments: `[...m.keys()].join(",")` on ints and `n.toString()` became
// `.map((k) => `${k}`).join(",")` and `String(n)`, which VTS translates.)
export function MxCleanupPure(props: { readonly label: string; readonly xs: readonly int[] }) {
  const [m, setM] = useState<ReadonlyMap<int, string>>(new Map([[1, "a"]]));
  const [n, setN] = useState<int>(0);
  invariant(m.size >= 1 && 0 <= n && n <= 10);
  useEffect(() => {
    const id = setTimeout(() => setN((k) => (k < 10 ? k + 1 : k)), Math.max(props.xs.length, 1) * 100 + props.label.trim().length);
    return () => {
      clearTimeout(id);
      if (m.has(1) && props.xs.some((x) => x > 0)) console.log("stop", [...m.keys()].map((k) => `${k}`).join(","), m.get(1)?.toUpperCase(), String(n));
      localStorage.setItem("m", JSON.stringify([...m.entries()]));
      document.title = props.xs.map((x) => x + 1).toSorted((a, b) => a - b).map((x) => `${x}`).join(" ");
    };
  }, [m, n, props.label, props.xs]);
  return <button onClick={() => setM(new Map(m).set(m.size + 1, props.label))}>{n}</button>;
}
