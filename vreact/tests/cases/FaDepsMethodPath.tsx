// expect: reject `s.trim` is a method, not a dependency
// A path through a method (`s.trim.length` is the method's arity, 0, for every string) is no
// dependency either; the message names the method link.
import { useState, useMemo } from "react";
import { type int } from "vreact/spec";

export function FaDepsMethodPath() {
  const [s, setS] = useState<string>(" a ");
  const k: int = useMemo(() => s.trim().length, [s.trim.length]);
  return <button type="button" onClick={() => setS("bcd")}>{k}</button>;
}
