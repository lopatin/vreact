// expect: verified update=verified append=verified moveLast=verified dup=verified firsts=verified clear=verified errors=none
import { ensures, requires, type int } from "vreact/spec";

// JS insertion order: set on a present key keeps its position
export function update(m: ReadonlyMap<int, string>, k: int, v: string): ReadonlyMap<int, string> {
  requires(m.has(k));
  ensures((r) => [...r.keys()].indexOf(k) === [...m.keys()].indexOf(k));
  ensures((r) => r.size === m.size);
  return new Map(m).set(k, v);
}

// set on a new key appends it
export function append(m: ReadonlyMap<int, string>, k: int, v: string): ReadonlyMap<int, string> {
  requires(!m.has(k));
  ensures((r) => [...r.keys()].indexOf(k) === m.size);
  ensures((r) => r.size === m.size + 1);
  return new Map(m).set(k, v);
}

// delete then set moves the key to the end
export function moveLast(m: ReadonlyMap<int, string>, k: int, v: string): ReadonlyMap<int, string> {
  ensures((r) => [...r.keys()].indexOf(k) === r.size - 1);
  const n = new Map(m);
  n.delete(k);
  n.set(k, v);
  return n;
}

// new Map(entries): a duplicate key keeps its first position and takes its last value
export function dup(): ReadonlyMap<int, string> {
  ensures((r) => r.size === 2 && r.get(1) === "c" && [...r.keys()][0] === 1 && [...r.keys()][1] === 2);
  return new Map<int, string>([[1, "a"], [2, "b"], [1, "c"]]);
}

// new Set(xs) keeps first occurrences, in order
export function firsts(): ReadonlySet<int> {
  ensures((r) => r.size === 2 && [...r][0] === 3 && [...r][1] === 1);
  return new Set([3, 1, 3]);
}

export function clear(s: ReadonlySet<string>, x: string): ReadonlySet<string> {
  ensures((r) => r.size === 1 && r.has(x));
  const n = new Set(s);
  n.clear();
  n.add(x);
  n.add(x);
  return n;
}
