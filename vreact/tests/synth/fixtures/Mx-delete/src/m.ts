import { ensures, hole, type int } from "vreact/spec";

// The fill must delete a key, which synth's grammar cannot (Maps and Sets only grow there): the
// closing hint says so
export function dropKey(m: ReadonlyMap<string, int>, k: string): ReadonlyMap<string, int> {
  ensures((r) => !r.has(k) && r.size >= m.size - 1 && [...r.keys()].every((x) => m.has(x)));
  return hole<ReadonlyMap<string, int>>();
}
