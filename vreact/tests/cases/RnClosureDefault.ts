// expect: reject a default value for parameter `x` of the local function h is not supported
// JS uses a default value when the argument is undefined: h(undefined) is 5, not undefined
// (the default was ignored).
import { type int, ensures } from "vreact/spec";

export function f(): int | undefined {
  ensures((r) => r === undefined);
  const h = function (x: int | undefined = 5): int | undefined {
    return x;
  };
  return h(undefined);
}
