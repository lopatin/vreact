// expect: reject `props.pair.length` is not a dependency path: `props.pair` is a tuple
// A tuple's `length` has no declaration, so it is not a data link: rejected, but before with a
// false reason ("is a method"). The advice is to list the tuple (`FaDepsOutsideValueOk.tsx`).
import { useState, useMemo } from "react";
import { invariant, type int } from "vreact/spec";

type P = { pair: readonly [int, string] };

export function FaDepsTupleLengthMsg(props: P) {
  const [n, setN] = useState<int>(0);
  const k: int = useMemo(() => n + props.pair[0], [n, props.pair.length]);
  invariant(n >= 0);
  return <button type="button" onClick={() => setN(k > 0 ? k : 0)}>{n}</button>;
}
