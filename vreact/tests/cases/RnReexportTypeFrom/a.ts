// expect: reject error TS1205: Re-exporting a type when 'isolatedModules' is enabled requires using 'export type'
// `export { Item } from "./types"` of a type: a per-file compiler keeps it, and the module fails
// to link (formerly VERIFIED).
import { type int, ensures } from "vreact/spec";
import { mk } from "./types";

export { Item } from "./types";

export function f(x: int): int {
  ensures((r) => r === x);
  return mk(x).id;
}
