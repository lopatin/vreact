// expect: verified verdict=verified
// A test next to the sources (cart.test.tsx, importing a test library) is skipped: vreact
// verifies the other files of "src".
import { useState } from "react";
import { type int, invariant } from "vreact/spec";

export function Cart() {
  const [q, setQ] = useState<int>(1);
  invariant(q >= 1);
  return <button type="button" onClick={() => { if (q < 5) setQ(q + 1); }}>{q}</button>;
}
