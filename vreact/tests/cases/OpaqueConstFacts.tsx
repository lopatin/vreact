// expect: verified
// A large constant is @opaque; a module-level assert(…) states (and proves once) the fact the
// components need — distinct ids — instead of unfolding 18 records into every proof.
import { assert, distinct, type int } from "vreact/spec";
type Seat = { readonly id: int; readonly row: int; readonly label: string };
/** @opaque */
export const SEATS: readonly Seat[] = [
  { id: 1, row: 0, label: "A1" },
  { id: 2, row: 0, label: "A2" },
  { id: 3, row: 0, label: "A3" },
  { id: 4, row: 0, label: "A4" },
  { id: 5, row: 0, label: "A5" },
  { id: 6, row: 0, label: "A6" },
  { id: 7, row: 1, label: "B1" },
  { id: 8, row: 1, label: "B2" },
  { id: 9, row: 1, label: "B3" },
  { id: 10, row: 1, label: "B4" },
  { id: 11, row: 1, label: "B5" },
  { id: 12, row: 1, label: "B6" },
  { id: 13, row: 2, label: "C1" },
  { id: 14, row: 2, label: "C2" },
  { id: 15, row: 2, label: "C3" },
  { id: 16, row: 2, label: "C4" },
  { id: 17, row: 2, label: "C5" },
  { id: 18, row: 2, label: "C6" },
];
assert(distinct(SEATS, (s) => s.id));
export const ROWS: readonly int[] = [0, 1, 2];
export function Grid() {
  return (
    <div>
      {ROWS.map((r) => (
        <div key={r}>
          {SEATS.filter((s) => s.row === r).map((s) => <span key={s.id}>{s.label}</span>)}
        </div>
      ))}
    </div>
  );
}
