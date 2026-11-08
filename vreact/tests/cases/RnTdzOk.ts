// expect: verified
// Initialisation order that JS runs without a ReferenceError: constants read (also through
// calls) only constants declared above them; `export default f` reads the (hoisted) function
// without calling it; the lambda of `ensures` is never called by the running code, so it may
// mention a constant declared below; a function declared below a constant may be called by it.
import { type int, ensures } from "vreact/spec";

export default twice;
export const BASE: int = 4;
export const DOUBLE: int = twice(BASE);
function twice(x: int): int {
  ensures((r) => r < LIMIT);
  return 2 * Math.min(x, 10);
}
export const LIMIT: int = 21;
const answer: int = DOUBLE + 1;
export { answer as theAnswer };

export function nine(): int {
  ensures((r) => r === 9);
  return answer;
}
