// expect: fail postcondition ok=verified
// False controls for `!==` map-updates: without distinct ids, and an exact count that is false.
import { requires, ensures, distinct, type int } from "vreact/spec";

type Task = { readonly id: int; readonly done: boolean };
export function activeCount(xs: readonly Task[]): int { return xs.filter((t) => !t.done).length; }
export function ok(xs: readonly Task[], id: int): readonly Task[] {
  requires(distinct(xs, (t) => t.id));
  ensures((r: readonly Task[]) => activeCount(r) <= activeCount(xs) + 1);
  return xs.map((t) => (t.id !== id ? t : { ...t, done: !t.done }));
}
export function noDistinct(xs: readonly Task[], id: int): readonly Task[] {
  ensures((r: readonly Task[]) => activeCount(r) <= activeCount(xs) + 1);
  return xs.map((t) => (t.id !== id ? t : { ...t, done: !t.done }));
}
export function exact(xs: readonly Task[], id: int): readonly Task[] {
  requires(distinct(xs, (t) => t.id));
  ensures((r: readonly Task[]) => activeCount(r) === activeCount(xs) + 1);
  return xs.map((t) => (t.id !== id ? t : { ...t, done: !t.done }));
}
