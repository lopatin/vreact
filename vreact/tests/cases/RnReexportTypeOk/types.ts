import { type int } from "vreact/spec";

export type Item = { readonly id: int };

export function mk(id: int): Item {
  return { id };
}
