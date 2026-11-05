// expect: fail postcondition
// False control for the map-update-by-key counts: toggling can raise the done count.
import { requires, ensures, distinct, type int } from "vreact/spec";

type Task = { readonly id: int; readonly done: boolean };

// toggling can raise the done count
export function grows(xs: readonly Task[], id: int): readonly Task[] {
  requires(distinct(xs, (t) => t.id));
  ensures((r: readonly Task[]) => r.filter((t) => t.done).length <= xs.filter((t) => t.done).length);
  return xs.map((t) => (t.id === id ? { ...t, done: !t.done } : t));
}
