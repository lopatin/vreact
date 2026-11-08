// expect: fail postcondition removeKey=incomplete differ=incomplete
// A generic contract is proved once for every instantiation: one that is false (removeKey: k may
// be absent), or true only at the calls in this module (differ), fails.
import { ensures, type int } from "vreact/spec";

export function removeKey<K extends int | string>(xs: readonly K[], k: K): readonly K[] {
  ensures((r: readonly K[]) => r.length < xs.length);
  return xs.filter((x) => x !== k);
}

export function differ<K extends int | string>(a: K, b: K): boolean {
  ensures((r: boolean) => r);
  return a !== b;
}

export function onlyCall(): boolean {
  return differ(1, 2) && differ("a", "b");
}
