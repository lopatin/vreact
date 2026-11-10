// expect: verified
// Fills inserted with the parentheses precedence requires (`hole<int>() * qty`, `-hole<int>()`).
import { requires, ensures, type int } from "vreact/spec";

export function total(base: int, qty: int): int {
  requires(qty >= 0);
  ensures((r: int) => r === (base + 1) * qty);
  return (base + 1) * qty;
}

export function negSucc(x: int): int {
  ensures((r: int) => r === 0 - x - 1);
  return -(x + 1);
}
