// expect: verified
// V5 (N16 residual): counts by key after a map-update guarded by `!==` (the condition is a
// negated key test after normalisation), in all three spellings.
import { requires, ensures, distinct, type int } from "vreact/spec";

type Task = { readonly id: int; readonly done: boolean; readonly prio: int };
export function activeCount(xs: readonly Task[]): int { return xs.filter((t) => !t.done).length; }
export function neTernary(xs: readonly Task[], id: int): readonly Task[] {
  requires(distinct(xs, (t) => t.id));
  ensures((r: readonly Task[]) => activeCount(r) <= activeCount(xs) + 1 && activeCount(xs) <= activeCount(r) + 1);
  return xs.map((t) => (t.id !== id ? t : { ...t, done: !t.done }));
}
export function blockNe(xs: readonly Task[], id: int): readonly Task[] {
  requires(distinct(xs, (t) => t.id));
  ensures((r: readonly Task[]) => activeCount(r) <= activeCount(xs) + 1);
  return xs.map((t) => {
    if (t.id !== id) return t;
    return { ...t, done: !t.done };
  });
}
export function neIdFirst(xs: readonly Task[], id: int): readonly Task[] {
  requires(distinct(xs, (t) => t.id));
  ensures((r: readonly Task[]) => activeCount(r) <= activeCount(xs) + 1);
  return xs.map((t) => (id !== t.id ? t : { ...t, done: !t.done }));
}
// finishing a present, active task: exactly one fewer
export function finishNe(xs: readonly Task[], i: int): readonly Task[] {
  requires(distinct(xs, (t) => t.id) && 0 <= i && i < xs.length && !xs[i].done);
  ensures((r: readonly Task[]) => activeCount(r) + 1 === activeCount(xs));
  const id = xs[i].id;
  return xs.map((t) => (t.id !== id ? t : { ...t, done: true }));
}
