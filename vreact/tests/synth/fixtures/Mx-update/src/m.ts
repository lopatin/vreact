import { ensures, hole, type int } from "vreact/spec";

// Map / Set updates are pure chains on fresh copies; random Maps have distinct keys in a random order
export function setCount(m: ReadonlyMap<string, int>, k: string, v: int): ReadonlyMap<string, int> {
  ensures((r) => r.get(k) === v && r.size >= m.size);
  return hole<ReadonlyMap<string, int>>();
}

export function addTag(s: ReadonlySet<string>, t: string): ReadonlySet<string> {
  ensures((r) => r.has(t) && [...s].every((x) => r.has(x)));
  return hole<ReadonlySet<string>>();
}

export function count(m: ReadonlyMap<int, string>): int {
  ensures((r) => r === [...m.keys()].length);
  return hole<int>();
}
