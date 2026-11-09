// expect: reject a type parameter inside a Set type (new Set<K>(xs)) is not supported yet
// As GxRejectMapTypeParam, for a Set built in a generic body.
import { type int } from "vreact/spec";

export function has<K extends int | string>(xs: readonly K[], k: K): boolean {
  const s = new Set<K>(xs);
  return s.has(k);
}
