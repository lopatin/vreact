// expect: verified
// N16: a map-update by key of a list with distinct keys changes a filter count by at most one
// (and, for the element with that key, by exactly its own change): the WIP-limit toggle.
import { useState } from "react";
import { invariant, requires, ensures, distinct, type int } from "vreact/spec";

type Task = { readonly id: int; readonly done: boolean; readonly prio: int };
const MAX_ACTIVE = 5;

// re-opening a done task is only allowed while under the limit
export function Wip() {
  const [tasks, setTasks] = useState<readonly Task[]>([]);
  invariant(distinct(tasks, (t) => t.id));
  invariant(tasks.filter((t) => !t.done).length <= MAX_ACTIVE);
  const active = tasks.filter((t) => !t.done).length;
  return (
    <ul>
      {tasks.map((t) => (
        <li key={t.id}>
          <button
            onClick={() => {
              if (t.done && active >= MAX_ACTIVE) return;
              setTasks(tasks.map((x) => (x.id === t.id ? { ...x, done: !x.done } : x)));
            }}
          >
            toggle
          </button>
        </li>
      ))}
    </ul>
  );
}

export function doneCount(xs: readonly Task[]): int {
  return xs.filter((t) => t.done).length;
}

export function toggle(xs: readonly Task[], id: int): readonly Task[] {
  requires(distinct(xs, (t) => t.id));
  ensures((r: readonly Task[]) => doneCount(r) <= doneCount(xs) + 1 && doneCount(xs) <= doneCount(r) + 1);
  return xs.map((t) => (t.id === id ? { ...t, done: !t.done } : t));
}

// the element with the key is known: the count changes exactly by its change
export function finish(xs: readonly Task[], i: int): readonly Task[] {
  requires(0 <= i && i < xs.length && distinct(xs, (t) => t.id) && !xs[i].done);
  ensures((r: readonly Task[]) => doneCount(r) === doneCount(xs) + 1);
  return xs.map((t) => (t.id === xs[i].id ? { ...t, done: true } : t));
}

// a count over a field the update does not touch is unchanged
export function bump(xs: readonly Task[], id: int): readonly Task[] {
  ensures((r: readonly Task[]) => r.filter((t) => t.done).length === xs.filter((t) => t.done).length);
  return xs.map((t) => (t.id === id ? { ...t, prio: t.prio + 1 } : t));
}
