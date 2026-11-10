// expect: reject Math.abs on a value of the type parameter K is not supported
import { type int } from "vreact/spec";

export function magnitude<K extends int>(k: K): number {
  return Math.abs(k);
}
