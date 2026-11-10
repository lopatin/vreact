// expect: reject import cycle
// A re-export loads its module like an import: a.ts re-exports from b.ts, which imports a.ts.
// Loading a.ts evaluates b.ts first, whose B reads A before a.ts has run (ReferenceError);
// formerly re-exports were not in the import graph and the cycle went unnoticed (Lean: A = 1,
// B = 2).
import { type int } from "vreact/spec";
export { B } from "./b";
export const A: int = 1;
