// Root component: holds the booking state.
import { useReducer } from "react";
import { invariant, distinct, type int } from "vreact/spec";
import { SEATS, ROWS, INITIAL, wellFormed, statusOf, type Seat } from "./model";
import { reducer } from "./reducer";
import { SeatButton } from "./components/SeatButton";
import { Summary } from "./components/Summary";

export function SeatsApp() {
  const [s, dispatch] = useReducer(reducer, INITIAL);
  invariant(wellFormed(s) && ROWS.every((r) => distinct(SEATS.filter((x: Seat) => x.row === r), (x: Seat) => x.id)));

  const free: int = SEATS.filter((x) => statusOf(s, x.id) === "free").length;

  return (
    <div className="app">
      <header>
        <h1>Seat booking</h1>
        <Summary selected={s.selected.length} booked={s.booked.length} free={free} max={s.max} />
      </header>
      <div className="venue">
        <div className="stage">stage</div>
        {ROWS.map((r) => (
          <div className="row" key={r}>
            {SEATS.filter((x: Seat) => x.row === r).map((x: Seat) => (
              <SeatButton
                key={x.id}
                seat={x}
                status={statusOf(s, x.id)}
                onToggle={(id) => dispatch({ kind: "toggle", seat: id })}
              />
            ))}
          </div>
        ))}
      </div>
      <div className="actions">
        <button disabled={s.selected.length === 0} onClick={() => dispatch({ kind: "clear", seat: 0 })}>
          Clear selection
        </button>
        <button disabled={s.selected.length === 0} onClick={() => dispatch({ kind: "confirm", seat: 0 })}>
          Confirm {s.selected.length} seat(s)
        </button>
      </div>
    </div>
  );
}
