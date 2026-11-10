// expect: reject error TS1292: 'Item' resolves to a type and must be marked type-only in this file before re-exporting
// `export default Item` of an imported type: a per-file compiler keeps the import and the
// export, and the module fails to link (formerly VERIFIED).
import { type int, ensures } from "vreact/spec";
import { Item, mk } from "./types";

export default Item;

export function f(x: int): int {
  ensures((r) => r === x);
  return mk(x).id;
}
