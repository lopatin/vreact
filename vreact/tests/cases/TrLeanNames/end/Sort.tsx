import { useState } from "react";
import { invariant, type int } from "vreact/spec";
import { at } from "../at";

export function Sort() {
  const [k, setK] = useState<int>(1);
  invariant(k >= 1);
  return <button onClick={() => setK(at(k))}>{k}</button>;
}
