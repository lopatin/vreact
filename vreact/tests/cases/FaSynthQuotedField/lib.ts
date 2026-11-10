import { type int } from "vreact/spec";

export type R = { readonly "my-field": int; readonly other: int };

export function fieldOf(p: R): int {
  const { "my-field": v } = p;
  return v;
}
