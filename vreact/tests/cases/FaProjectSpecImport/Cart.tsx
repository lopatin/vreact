// expect: reject src/order.spec.ts is part of the TypeScript program (through an import or a `/// <reference>`) but is not one of the verified sources: its name contains ".test." or ".spec.", and vreact skips such files in "src" (as tests); rename it
// vreact skips files named *.test.* / *.spec.* in "src" (tests): importing one is rejected, and
// the message says why (not "declarations outside the verified program").
import { useState } from "react";
import { type int, invariant } from "vreact/spec";
import { maxQty } from "./order.spec";

export function Cart() {
  const [q, setQ] = useState<int>(1);
  invariant(q >= 1);
  return <button type="button" onClick={() => { if (q < maxQty()) setQ(q + 1); }}>{q}</button>;
}
