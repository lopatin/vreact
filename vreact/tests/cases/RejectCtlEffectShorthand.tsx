// expect: reject useEffect is missing dependencies: index
// The exhaustive-deps check resolves shorthand properties in effects too.
import { useState, useEffect } from "react";
import { type int } from "vreact/spec";
type Sel = { readonly index: int };
export function CtlEffectDeps() {
  const [index, setIndex] = useState<int>(2);
  const [sel, setSel] = useState<Sel>({ index: 0 });
  useEffect(() => {
    setSel({ index });
  }, []);
  return <button onClick={() => setIndex(index + 1)}>{sel.index}</button>;
}
