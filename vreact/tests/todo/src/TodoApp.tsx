import { useState } from "react";
import { invariant, distinct, type int } from "vreact/spec";
import type { Todo, Filter } from "./types";
import { TodoItem } from "./TodoItem";

const MAX_LEN = 100;

function visible(todos: readonly Todo[], f: Filter): readonly Todo[] {
  if (f === "all") return todos;
  return todos.filter((t) => (f === "done" ? t.done : !t.done));
}

export function TodoApp() {
  const [todos, setTodos] = useState<readonly Todo[]>([]);
  const [nextId, setNextId] = useState<int>(1);
  const [draft, setDraft] = useState<string>("");
  const [filter, setFilter] = useState<Filter>("all");
  invariant(distinct(todos, (t) => t.id));
  invariant(todos.every((t) => t.id < nextId && t.text.length > 0));
  invariant(draft.length <= MAX_LEN);

  const shown = visible(todos, filter);
  const remaining = todos.filter((t) => !t.done).length;

  const add = () => {
    const text = draft.trim();
    if (text.length === 0) return;
    setTodos([...todos, { id: nextId, text, done: false }]);
    setNextId(nextId + 1);
    setDraft("");
  };

  return (
    <div>
      <input
        value={draft}
        onChange={(e) => {
          if (e.target.value.length <= MAX_LEN) setDraft(e.target.value);
        }}
      />
      <button disabled={draft.trim().length === 0} onClick={add}>Add</button>
      <ul>
        {shown.map((t) => (
          <TodoItem
            key={t.id}
            todo={t}
            onToggle={(id) => setTodos(todos.map((x) => (x.id === id ? { ...x, done: !x.done } : x)))}
            onDelete={(id) => setTodos(todos.filter((x) => x.id !== id))}
          />
        ))}
      </ul>
      <p>{remaining} left</p>
      <button onClick={() => setFilter("all")}>All</button>
      <button onClick={() => setFilter("active")}>Active</button>
      <button onClick={() => setFilter("done")}>Done</button>
    </div>
  );
}
