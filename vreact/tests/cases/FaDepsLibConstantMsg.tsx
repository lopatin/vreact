// expect: reject `Number.MAX_SAFE_INTEGER` is not a dependency path: `MAX_SAFE_INTEGER` is declared by a library
// A library constant listed as a dependency is not a data path (only fields the program declares,
// `length` and `size` are): rejected, but before with a false reason ("is a method ... list the
// value it is called on (`Number`)"). The advice is to leave it out: the check never requires a
// value from outside the component.
import { useState, useMemo } from "react";
import { invariant, type int } from "vreact/spec";

export function FaDepsLibConstantMsg() {
  const [n, setN] = useState<int>(0);
  const k: int = useMemo(() => n + 1, [n, Number.MAX_SAFE_INTEGER]);
  invariant(n >= 0);
  return <button type="button" onClick={() => setN(k)}>{n}</button>;
}
