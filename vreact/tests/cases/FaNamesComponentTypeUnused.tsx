// expect: reject `Todo` names both a type (line 6) and a component of this module
// The same clash where only a function uses the type (and its field `init` would meet the
// component's `init`): rejected with the clash message too.
import { useState } from "react";
import { type int, ensures } from "vreact/spec";
export type Todo = { readonly id: int; readonly init: int };

export function count(xs: readonly Todo[]): int {
  ensures((r) => r >= 0);
  return xs.length;
}

export function Todo({ text }: { readonly text: string }) {
  const [open, setOpen] = useState<boolean>(false);
  return <li onClick={() => setOpen(!open)}>{text}</li>;
}
