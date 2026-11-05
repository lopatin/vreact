// The cart reducer: total (no requires), delegates to the model.
import { ensures, implies, type int } from "vreact/spec";
import { type Line, wellFormed, add, remove, inc, dec } from "./model";

export type Action = { readonly kind: "add" | "remove" | "inc" | "dec"; readonly id: int };

export function reducer(s: readonly Line[], a: Action): readonly Line[] {
  ensures((r: readonly Line[]) => implies(wellFormed(s), wellFormed(r)));
  switch (a.kind) {
    case "add":
      return add(s, a.id);
    case "remove":
      return remove(s, a.id);
    case "inc":
      return inc(s, a.id);
    case "dec":
      return dec(s, a.id);
  }
}
