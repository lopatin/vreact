import { requires, idiv, type int } from "vreact/spec";

type StatsProps = { readonly todo: int; readonly doing: int; readonly done: int; readonly points: int };

/** Totals and progress. Division is guarded: an empty board is 0% done. */
export function Stats(props: StatsProps) {
  requires(props.todo >= 0 && props.doing >= 0 && props.done >= 0);
  const total = props.todo + props.doing + props.done;
  const pct = total === 0 ? 0 : idiv(props.done * 100, total);
  return (
    <div className="stats">
      <span>{total} cards</span>
      <span>{props.points} points</span>
      <span>{pct}% done</span>
      <progress max={100} value={pct} />
    </div>
  );
}
