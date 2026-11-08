// expect: reject new Map(…) of [key, value] pairs computed by a callback: write the types: new Map<K, V>(…)
import { type int } from "vreact/spec";

export type Order = { readonly id: int; readonly name: string };

// TypeScript infers Map<number, Order>; VTS needs the key type (int, not number)
export function count(xs: readonly Order[]): int {
  const byId = new Map(xs.map((x) => [x.id, x]));
  return byId.size;
}
