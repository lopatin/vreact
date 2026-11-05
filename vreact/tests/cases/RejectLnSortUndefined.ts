// expect: reject toSorted on an array that may contain undefined
/// <reference lib="es2023.array" />
// JS sorts undefined elements to the end without calling the comparator; the model
// would pass them to it.
import { type int } from "vreact/spec";

export function sortOpt(xs: readonly (int | undefined)[]): readonly (int | undefined)[] {
  return xs.toSorted((a, b) => (a ?? 0) - (b ?? 0));
}
