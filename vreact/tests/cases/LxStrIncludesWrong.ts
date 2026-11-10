// expect: fail postcondition
// False control for the literal-string simprocs: "ab" contains no "@".
import { ensures } from "vreact/spec";

export function noAt(): boolean {
  ensures((r: boolean) => r === true);
  return "ab".includes("@") || "hello".startsWith("lo");
}
