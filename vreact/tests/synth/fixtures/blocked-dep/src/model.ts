import { ensures, type int } from "vreact/spec";

export type Level = { readonly value: int };

// a false postcondition: modules importing this one are not checked
export function grow(l: Level): Level {
  ensures((r: Level) => r.value > l.value);
  return { value: l.value };
}
