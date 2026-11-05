import { callbackRequires, type int } from "vreact/spec";
import { type Seat, type SeatStatus } from "../model";

export type SeatButtonProps = {
  readonly seat: Seat;
  readonly status: SeatStatus;
  readonly onToggle: (id: int) => void;
};

/** One seat. It only ever reports its own seat id to the parent. */
export function SeatButton(props: SeatButtonProps) {
  callbackRequires(props.onToggle, (id) => id === props.seat.id);
  return (
    <button
      className={`seat seat-${props.status}`}
      disabled={props.status === "booked"}
      aria-pressed={props.status === "selected"}
      title={`${props.seat.label} (${props.status})`}
      onClick={() => props.onToggle(props.seat.id)}
    >
      {props.seat.label}
    </button>
  );
}
