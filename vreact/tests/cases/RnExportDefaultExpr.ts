// expect: reject `export default` of an expression is not supported
// `export default <expression>` runs the expression when the module loads (here an index out of
// bounds and a read of XS); formerly skipped, so nothing about it was checked.
import { type int } from "vreact/spec";

export const XS: readonly int[] = [1, 2];
export default XS[5] + XS.length;
