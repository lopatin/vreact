// expect: reject `Todo` names both a type (line 6) and a component of this module
// A component named like a type of its module gets the documented name-clash message (both
// would be VTS.<module>.Todo), not "unsupported type declaration" at the component: the type
// reference resolves to the type of the merged symbol.
import { useState } from "react";
export type Todo = { readonly id: number; readonly text: string; readonly done: boolean };

export function Todo({ todo }: { readonly todo: Todo }) {
  const [open, setOpen] = useState<boolean>(false);
  return <li onClick={() => setOpen(!open)}>{todo.text}</li>;
}

export function List() {
  const items: readonly Todo[] = [{ id: 1, text: "a", done: false }];
  return <ul>{items.map((t) => <Todo key={t.id} todo={t} />)}</ul>;
}
