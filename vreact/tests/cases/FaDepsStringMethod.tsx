// expect: reject `s.trim` is a method, not a dependency
// A string method as a dependency: `s.trim` is String.prototype.trim for every string, so React
// would keep the first length after `s` changes, while the model recomputes it.
import { useState, useMemo } from "react";
import { type int } from "vreact/spec";

export function FaDepsStringMethod() {
  const [s, setS] = useState<string>(" a ");
  const k: int = useMemo(() => s.trim().length, [s.trim]);
  return <button type="button" onClick={() => setS("bcd")}>{k}</button>;
}
