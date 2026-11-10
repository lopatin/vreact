// expect: reject module name clash
// Todo.tsx and todo.ts become VTS.Todo and VTS.todo, whose generated files
// VTS/Todo/… and VTS/todo/… are the same files on a case-insensitive disk.
import { type Item } from "./todo";
export function Todo() {
  const it: Item = { id: 1 };
  return <p>{it.id}</p>;
}
