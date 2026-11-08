// expect: fail postcondition
import { ensures, type int } from "vreact/spec";

type MxeowItem = { readonly id: int; readonly name: string };

// wrong: the key was just set, so r.get(it.id)?.name is the item's name, never undefined
export function put(m: ReadonlyMap<int, MxeowItem>, it: MxeowItem): ReadonlyMap<int, MxeowItem> {
  ensures((r) => r.get(it.id)?.name === undefined);
  return new Map(m).set(it.id, it);
}
