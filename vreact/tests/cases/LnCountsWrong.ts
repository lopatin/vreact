// expect: fail postcondition
// The count lemmas must not prove a false bound: with duplicate ids, marking "the" task
// with id `id` done can complete several tasks at once.
import { requires, ensures, type int } from "vreact/spec";

type Task = { readonly id: int; readonly done: boolean };

export function markDone(xs: readonly Task[], id: int): readonly Task[] {
  requires(xs.filter((t) => t.done).length < 3);
  ensures((r: readonly Task[]) => r.filter((t) => t.done).length <= 3);
  return xs.map((t) => (t.id === id ? { ...t, done: true } : t));
}
