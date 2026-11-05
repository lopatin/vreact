// expect: verified
// Counts (`filter(p).length`) under delete, mark-all-done and map-updates by id.
import { useState } from "react";
import { invariant, requires, ensures, distinct, type int } from "vreact/spec";

type Task = { readonly id: int; readonly done: boolean; readonly prio: int };
const MAX_ACTIVE = 5;

export function LnLimited() {
  const [tasks, setTasks] = useState<readonly Task[]>([]);
  const [nextId, setNextId] = useState<int>(0);
  invariant(distinct(tasks, (t) => t.id) && tasks.every((t) => t.id < nextId));
  invariant(tasks.filter((t) => !t.done).length <= MAX_ACTIVE);
  const active = tasks.filter((t) => !t.done).length;
  return (
    <div>
      <button
        onClick={() => {
          if (active >= MAX_ACTIVE) return;
          setTasks([...tasks, { id: nextId, done: false, prio: 0 }]);
          setNextId(nextId + 1);
        }}
      >
        add
      </button>
      <ul>
        {tasks.map((t) => (
          <li key={t.id}>
            <button onClick={() => setTasks(tasks.filter((x) => x.id !== t.id))}>del</button>
            <button onClick={() => setTasks(tasks.map((x) => (x.id === t.id ? { ...x, done: true } : x)))}>done</button>
          </li>
        ))}
      </ul>
      <button onClick={() => setTasks(tasks.map((x) => ({ ...x, done: true })))}>all done</button>
      <button onClick={() => setTasks(tasks.filter((x) => !x.done))}>clear done</button>
    </div>
  );
}

export function partition(xs: readonly Task[]): int {
  ensures((r: int) => r === xs.length);
  return xs.filter((t) => t.done).length + xs.filter((t) => !t.done).length;
}

export function removeOne(xs: readonly Task[], id: int): readonly Task[] {
  requires(distinct(xs, (t) => t.id) && xs.some((t) => t.id === id));
  ensures((r: readonly Task[]) => r.length === xs.length - 1);
  return xs.filter((t) => t.id !== id);
}

export function capPrio(xs: readonly Task[]): readonly Task[] {
  requires(xs.filter((t) => t.prio > 5).length <= 2);
  ensures((r: readonly Task[]) => r.filter((t) => t.prio > 5).length <= 2);
  return xs.map((t) => (t.prio > 5 ? t : { ...t, prio: Math.min(t.prio, 5) }));
}
