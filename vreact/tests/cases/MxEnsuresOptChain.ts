// expect: verified
import { ensures, type int } from "vreact/spec";

type MxeoItem = { readonly id: int; readonly name: string; readonly tags: readonly string[] };

// contracts on an unannotated result parameter: `?.`, `!` and longer chains on r.get(k), and
// array methods on an array result (the nullish value of each part comes from the declared types)
export function put(m: ReadonlyMap<int, MxeoItem>, it: MxeoItem): ReadonlyMap<int, MxeoItem> {
  ensures((r) => r.get(it.id)?.name === it.name);
  ensures((r) => r.get(it.id)!.tags.length === it.tags.length);
  ensures((r) => r.get(it.id)?.tags.length === it.tags.length);
  ensures((r) => r.get(it.id)?.tags.at(0) === it.tags.at(0));
  ensures((r) => r.get(it.id + 1)?.name === m.get(it.id + 1)?.name);
  return new Map(m).set(it.id, it);
}

export function firsts(xs: readonly MxeoItem[]): readonly MxeoItem[] {
  ensures((r) => r.at(0)?.name === xs.at(0)?.name);
  ensures((r) => r.at(-1)?.id === xs.at(-1)?.id);
  return [...xs];
}
