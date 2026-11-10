// expect: reject VTS requires "strict": true, with strictNullChecks
// "strict": true with "strictNullChecks": false: TypeScript types then say nothing about null and
// undefined (`r === null` below would pass the null/undefined check and be read as "absent").
import { ensures, type int } from "vreact/spec";
export function f(): int | undefined {
  ensures((r) => r === null);
  return undefined;
}
