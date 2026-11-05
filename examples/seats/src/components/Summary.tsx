import { requires, type int } from "vreact/spec";

export type SummaryProps = {
  readonly selected: int;
  readonly booked: int;
  readonly free: int;
  readonly max: int;
};

/** Counts. The parent guarantees 0 <= selected <= max. */
export function Summary(props: SummaryProps) {
  requires(0 <= props.selected && props.selected <= props.max);
  const remaining: int = props.max - props.selected;
  return (
    <div className="stats">
      <span>
        Selected <b>{props.selected}</b> / {props.max}
      </span>
      <span className="meter">{"●".repeat(props.selected) + "○".repeat(remaining)}</span>
      <span>
        Booked <b>{props.booked}</b>
      </span>
      <span>
        Free <b>{props.free}</b>
      </span>
      {remaining === 0 ? <span className="limit">limit reached</span> : <span>{remaining} more allowed</span>}
    </div>
  );
}
