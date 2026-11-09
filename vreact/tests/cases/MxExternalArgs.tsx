// expect: verified
import { useState } from "react";
import { invariant, type int } from "vreact/spec";

type R = { readonly a: int; readonly b: string };
// the arguments of external writes are checked as VTS expressions: ordinary logging keeps working
export function MxExternalArgs(props: { readonly label: string; readonly xs: readonly int[] }) {
  const [s, setS] = useState<ReadonlyMap<int, int>>(new Map([[1, 1]]));
  const [r, setR] = useState<R>({ a: 1, b: "x" });
  invariant(s.size >= 1);
  return (
    <button
      onClick={() => {
        console.log("click", props.label, s.size, [...s.keys()], r.a);
        console.log(JSON.stringify(r), JSON.stringify(props.xs, null, 2));
        console.log(null, undefined, `n=${s.size}`, new Map(s).set(2, 2).size);
        console.warn(String(s.size));
        localStorage.setItem("n", String(s.size));
        document.title = `${props.label}: ${s.size}`;
        setS(new Map(s).set(2, 2));
        setR({ ...r, a: r.a + 1 });
      }}
    >
      {s.size}
    </button>
  );
}
