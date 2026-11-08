// expect: reject Math.floor on a value of the type parameter T is not supported: its values are abstract
// Math.floor/trunc/round/ceil/abs read their argument as a number: not a value of T.
import { type int } from "vreact/spec";

export function down<T extends int>(x: T): number {
  return Math.floor(x);
}
