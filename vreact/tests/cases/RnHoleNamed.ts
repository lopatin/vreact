// expect: verified
// A project function spelled `hole` is not vreact/spec's hole(): the contract of a function
// calling it is proved (formerly it was left `sorry /- pending: hole() -/`, INCOMPLETE).
import { type int, ensures } from "vreact/spec";

function hole(): int {
  return 1;
}

export function f(x: int): int {
  ensures((r) => r === x + 1);
  return x + hole();
}
