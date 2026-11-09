// expect: verified
import { ensures, type int } from "vreact/spec";

// A fresh local Map / Set named `console` is the program's own variable, not the global console:
// `console.add(1)` is a mutation of it (not logging), and the translation keeps it.
export function one(): int {
  ensures((r) => r === 1);
  const console = new Set<int>();
  console.add(1);
  return console.size;
}

export function two(): int {
  ensures((r) => r === 2);
  const console = new Map<string, int>([["a", 1]]);
  console.set("b", 2);
  return console.size;
}

// in a loop: the for…of fold carries the Set (not `fun acc x => acc`)
export function loop(xs: readonly int[]): ReadonlySet<int> {
  ensures((r) => xs.every((x) => r.has(x)));
  const console = new Set<int>();
  for (const x of xs) console.add(x);
  return console;
}

export function cleared(xs: readonly int[]): int {
  ensures((r) => r === 0);
  const localStorage = new Set<int>(xs);
  localStorage.clear();
  return localStorage.size;
}
