import { callbackRequires, type int } from "vreact/spec";
import type { Card, ColumnId } from "../model";

type CardViewProps = {
  readonly card: Card;
  readonly col: ColumnId;
  readonly selected: boolean;
  readonly onMove: (id: int, to: ColumnId) => void;
  readonly onDelete: (id: int) => void;
  readonly onSelect: (id: int) => void;
};

/** One card. It only ever reports its own id, and only moves to an adjacent column. */
export function CardView(props: CardViewProps) {
  callbackRequires(props.onMove, (id, to) => id === props.card.id && to !== props.col);
  callbackRequires(props.onDelete, (id) => id === props.card.id);
  callbackRequires(props.onSelect, (id) => id === props.card.id);
  const left: ColumnId | null = props.col === "done" ? "doing" : props.col === "doing" ? "todo" : null;
  const right: ColumnId | null = props.col === "todo" ? "doing" : props.col === "doing" ? "done" : null;
  return (
    <li className={props.selected ? "card selected" : "card"}>
      <button className="title" onClick={() => props.onSelect(props.card.id)}>
        {props.card.title}
      </button>
      <span className="points">{props.card.points}</span>
      <span className="actions">
        {left !== null && <button aria-label="move left" onClick={() => props.onMove(props.card.id, left)}>←</button>}
        {right !== null && <button aria-label="move right" onClick={() => props.onMove(props.card.id, right)}>→</button>}
        <button aria-label="delete" onClick={() => props.onDelete(props.card.id)}>✕</button>
      </span>
    </li>
  );
}
