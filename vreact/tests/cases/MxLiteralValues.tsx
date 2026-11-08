// expect: verified
import { useState } from "react";
import { ensures, invariant, type int } from "vreact/spec";

// values of a literal Map, of two literal entries, and of a set on an empty Map
export function mxlvOne(): ReadonlyMap<string, int> {
  ensures((r) => [...r.values()].every((v) => v >= 0));
  return new Map<string, int>([["apple", 1]]);
}

export function mxlvTwo(): ReadonlyMap<string, int> {
  ensures((r) => [...r.values()].every((v) => v >= 0));
  ensures((r) => r.size === 2);
  return new Map<string, int>([["apple", 1], ["pear", 2]]);
}

export function mxlvSetEmpty(k: string): ReadonlyMap<string, int> {
  ensures((r) => [...r.values()].every((v) => v === 1));
  return new Map<string, int>().set(k, 1);
}

// a non-empty literal initial state under a values invariant
export function MxLiteralValues() {
  const [qty, setQty] = useState<ReadonlyMap<string, int>>(new Map([["apple", 1], ["pear", 0]]));
  invariant([...qty.values()].every((v) => v >= 0));
  return (
    <ul>
      {[...qty.keys()].map((k) => (
        <li key={k} onClick={() => setQty(new Map(qty).set(k, (qty.get(k) ?? 0) + 1))}>
          {k}
        </li>
      ))}
    </ul>
  );
}
