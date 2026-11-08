// expect: reject is a number here, not a string
// An <li>'s value is a number: the event model's `value` (a string) does not describe it.
import { useState } from "react";
import { invariant } from "vreact/spec";
export function RjEventNumber() {
  const [s, setS] = useState<string>("");
  invariant(s.length >= 0);
  return <ul><li onClick={(e) => setS(String(e.currentTarget.value))}>{s}</li></ul>;
}
