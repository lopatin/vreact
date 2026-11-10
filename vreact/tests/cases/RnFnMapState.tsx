// expect: reject state `m` has the function type (x: int) => int (field f of Box), which is not data
// A Map of records with a function field as state.
import { useState } from "react";
import { type int } from "vreact/spec";

type Box = { readonly f: (x: int) => int; readonly n: int };

export function C() {
  const [m] = useState<ReadonlyMap<int, Box>>(new Map());
  return <p>{m.size}</p>;
}
