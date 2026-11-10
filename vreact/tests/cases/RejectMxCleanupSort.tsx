// expect: reject effect cleanups may not call `p.xs.sort` here (it mutates p.xs)
import { useEffect, useState } from "react";
import { invariant, type int } from "vreact/spec";

type P = { readonly xs: int[] };
// a mutator reached through a field of the state record (in a cleanup condition)
export function Sorted() {
  const [p, setP] = useState<P>({ xs: [2, 1] });
  invariant(p.xs.length === 0 || p.xs[0] === 2);
  useEffect(() => {
    return () => {
      if (p.xs.sort().length > 0) console.log("sorted");
    };
  }, [p]);
  return <button onClick={() => setP({ xs: [...p.xs] })}>{p.xs.length}</button>;
}
