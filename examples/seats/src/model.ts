// Seat booking model: venue, state, invariant and pure operations.
import { ensures, distinct, implies, hole, type int } from "vreact/spec";

export type Seat = { readonly id: int; readonly row: int; readonly label: string };

/** The venue: 3 rows x 6 seats, id = 10 * row + column (unique). */
export const SEATS: readonly Seat[] = [
  { id: 1, row: 0, label: "A1" },
  { id: 2, row: 0, label: "A2" },
  { id: 3, row: 0, label: "A3" },
  { id: 4, row: 0, label: "A4" },
  { id: 5, row: 0, label: "A5" },
  { id: 6, row: 0, label: "A6" },
  { id: 11, row: 1, label: "B1" },
  { id: 12, row: 1, label: "B2" },
  { id: 13, row: 1, label: "B3" },
  { id: 14, row: 1, label: "B4" },
  { id: 15, row: 1, label: "B5" },
  { id: 16, row: 1, label: "B6" },
  { id: 21, row: 2, label: "C1" },
  { id: 22, row: 2, label: "C2" },
  { id: 23, row: 2, label: "C3" },
  { id: 24, row: 2, label: "C4" },
  { id: 25, row: 2, label: "C5" },
  { id: 26, row: 2, label: "C6" },
];

export const ROWS: readonly int[] = [0, 1, 2];

export const MAX_SELECTION: int = 4;

export type Booking = {
  readonly booked: readonly int[];
  readonly selected: readonly int[];
  readonly max: int;
};

export type SeatStatus = "free" | "selected" | "booked";

export function isSeat(id: int): boolean {
  return SEATS.some((s) => s.id === id);
}

/** The state invariant. */
export function wellFormed(b: Booking): boolean {
  return (
    distinct(b.booked) &&
    distinct(b.selected) &&
    b.booked.every((x) => isSeat(x)) &&
    b.selected.every((x) => isSeat(x)) &&
    b.selected.every((x) => !b.booked.includes(x)) &&
    b.selected.length <= b.max
  );
}

/** Same elements (as sets). */
export function sameSet(a: readonly int[], b: readonly int[]): boolean {
  return a.every((x) => b.includes(x)) && b.every((x) => a.includes(x));
}

/** Whether a not-yet-selected seat may be added to the selection. */
export function canSelect(b: Booking, id: int): boolean {
  return isSeat(id) && !b.booked.includes(id) && b.selected.length < b.max;
}

export function statusOf(b: Booking, id: int): SeatStatus {
  if (b.booked.includes(id)) return "booked";
  if (b.selected.includes(id)) return "selected";
  return "free";
}

export const INITIAL: Booking = { booked: [3, 4, 14, 22], selected: [], max: MAX_SELECTION };

/**
 * Toggle the selection of a seat: deselect if selected; select if allowed; otherwise ignore.
 * @opaque
 */
export function toggle(b: Booking, id: int): Booking {
  ensures((r: Booking) => implies(wellFormed(b), wellFormed(r)));
  ensures((r: Booking) => r.max === b.max);
  ensures((r: Booking) => sameSet(r.booked, b.booked));
  ensures((r: Booking) => implies(b.selected.includes(id), !r.selected.includes(id)));
  ensures((r: Booking) => implies(!b.selected.includes(id), r.selected.includes(id) === canSelect(b, id)));
  ensures((r: Booking) => r.selected.every((x) => x === id || b.selected.includes(x)));
  ensures((r: Booking) => b.selected.every((x) => x === id || r.selected.includes(x)));
  if (b.selected.includes(id)) return { ...b, selected: b.selected.filter((x) => x !== id) };
  if (!canSelect(b, id)) return b;
  return { ...b, selected: [...b.selected, id] };
}

/**
 * Empty the selection.
 * @opaque
 */
export function clear(b: Booking): Booking {
  ensures((r: Booking) => implies(wellFormed(b), wellFormed(r)));
  ensures((r: Booking) => r.max === b.max);
  ensures((r: Booking) => sameSet(r.booked, b.booked));
  ensures((r: Booking) => r.selected.length === 0);
  return { ...b, selected: [] };
}

/**
 * Book the selected seats; the selection becomes empty.
 * @opaque
 */
export function confirm(b: Booking): Booking {
  ensures((r: Booking) => implies(wellFormed(b), wellFormed(r)));
  ensures((r: Booking) => r.max === b.max);
  ensures((r: Booking) => r.selected.length === 0);
  ensures((r: Booking) => r.booked.every((x) => b.booked.includes(x) || b.selected.includes(x)));
  ensures((r: Booking) => b.booked.every((x) => r.booked.includes(x)));
  ensures((r: Booking) => b.selected.every((x) => r.booked.includes(x)));
  return { ...b, booked: [...b.booked, ...b.selected], selected: [] };
}
