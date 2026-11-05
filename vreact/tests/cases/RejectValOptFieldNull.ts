// expect: reject can be undefined but never null
// An optional field is undefined when absent: `t.due === null` is always false in JS.
import { type int } from "vreact/spec";

type Task = { readonly id: int; readonly due?: int };

export function hasNoDue(t: Task): boolean {
  return t.due === null;
}
