// expect: verified verdict=verified App=verified App.certificate=verified upsertById=verified removeById=verified
// Generic @opaque helpers of another module, used by a component through their polymorphic
// contracts (instantiated at T := Todo, with the accessor fun t => t.id).
import { useState } from "react";
import { invariant, distinct, type int } from "vreact/spec";
import { upsertById, removeById, type Todo } from "./lib";

export function App() {
  const [todos, setTodos] = useState<readonly Todo[]>([]);
  const [next, setNext] = useState<int>(1);
  invariant(distinct(todos, (t) => t.id));
  return (
    <div>
      <button
        onClick={() => {
          setTodos(upsertById(todos, { id: next, title: "new", done: false }));
          setNext(next + 1);
        }}
      >
        add
      </button>
      {todos.map((t) => (
        <p key={t.id}>
          {t.title}
          <button onClick={() => setTodos(removeById(todos, t.id))}>x</button>
          <button onClick={() => setTodos(upsertById(todos, { ...t, done: !t.done }))}>toggle</button>
        </p>
      ))}
    </div>
  );
}
