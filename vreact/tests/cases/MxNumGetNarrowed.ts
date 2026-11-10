// expect: verified
// …and following the advice is accepted.
import { ensures, type int } from "vreact/spec";

export function f2(m: ReadonlyMap<int, number>): boolean {
  ensures((r: boolean) => !r || m.has(1));
  const v = m.get(1);
  if (v !== undefined) return v === 1.5;
  return false;
}
