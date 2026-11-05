// expect: fail handler
// False control for the map-update-by-key counts: the bound needs distinct keys.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";

type Task = { readonly id: int; readonly done: boolean };

// without distinct ids one toggle may re-open several tasks
export function WipNoDistinct() {
  const [tasks, setTasks] = useState<readonly Task[]>([]);
  invariant(tasks.filter((t) => !t.done).length <= 5);
  const active = tasks.filter((t) => !t.done).length;
  return (
    <button
      onClick={() => {
        if (tasks.length === 0) return;
        const t = tasks[0];
        if (t.done && active >= 5) return;
        setTasks(tasks.map((x) => (x.id === t.id ? { ...x, done: !x.done } : x)));
      }}
    >
      toggle
    </button>
  );
}
