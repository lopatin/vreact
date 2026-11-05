import { callbackRequires } from "vreact/spec";
import type { Todo } from "./types";
import type { int } from "vreact/spec";

type TodoItemProps = {
  readonly todo: Todo;
  readonly onToggle: (id: int) => void;
  readonly onDelete: (id: int) => void;
};

export function TodoItem(props: TodoItemProps) {
  callbackRequires(props.onToggle, (id) => id === props.todo.id);
  callbackRequires(props.onDelete, (id) => id === props.todo.id);
  return (
    <li className={props.todo.done ? "done" : ""}>
      <input type="checkbox" checked={props.todo.done} onChange={() => props.onToggle(props.todo.id)} />
      <span>{props.todo.text}</span>
      <button onClick={() => props.onDelete(props.todo.id)}>×</button>
    </li>
  );
}
