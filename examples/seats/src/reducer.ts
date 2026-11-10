// The booking reducer: total, delegates to the model.
import { ensures, implies, type int } from "vreact/spec";
import { type Booking, wellFormed, toggle, clear, confirm } from "./model";

export type ActionKind = "toggle" | "clear" | "confirm";

/** `seat` is only meaningful for "toggle". */
export type Action = { readonly kind: ActionKind; readonly seat: int };

export function reducer(s: Booking, a: Action): Booking {
  ensures((r: Booking) => implies(wellFormed(s), wellFormed(r)));
  switch (a.kind) {
    case "toggle":
      return toggle(s, a.seat);
    case "clear":
      return clear(s);
    case "confirm":
      return confirm(s);
  }
}
