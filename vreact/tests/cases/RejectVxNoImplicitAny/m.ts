// expect: reject VTS requires "strict": true, with noImplicitAny
// "strict": false with "strictNullChecks": true: an unannotated parameter is then implicitly `any`,
// which TypeScript checks nothing about (`r.every((x) => isNull(x))` below passes undefined elements).
import { ensures, type int } from "vreact/spec";
export function isNull(x: int | null): boolean {
  return x === null;
}
export function f(n: int): readonly (int | undefined)[] {
  ensures((r) => r.every((x) => isNull(x)));
  return [undefined, undefined];
}
