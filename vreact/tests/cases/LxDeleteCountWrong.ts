// expect: fail postcondition
// False control for the counting facts of a delete by key: without distinct ids, filtering out
// the selected element's id may remove more than one element.
import { requires, ensures, type int } from "vreact/spec";

type Item = { readonly id: int; readonly name: string };

export function removeSome(items: readonly Item[], sel: int): readonly Item[] {
  requires(0 <= sel && sel < items.length);
  ensures((r: readonly Item[]) => r.length === items.length - 1);
  return items.filter((i) => i.id !== items[sel].id);
}
