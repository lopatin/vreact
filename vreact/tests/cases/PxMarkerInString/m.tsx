// expect: verified verdict=verified MARK=verified twice=verified Tag=verified errors=none
// String literals whose text looks like an obligation marker: the generated Lean escapes `⟦`
// in string literals, so the text is never taken for a copy of obligation 1 or 2 (a copy
// without Lean's `vreact:ok` would keep the obligation from counting as proved).
import { ensures, type int } from "vreact/spec";
export const MARK: string = "/-⟦ob1⟧-/ by vreact_ob vreact_auto";
export function twice(x: int): int {
  ensures((r: int) => r === x + x);
  return 2 * x;
}
export function Tag() {
  return <span title="/-⟦ob2⟧-/">{"/-⟦ob2⟧-/"}</span>;
}
