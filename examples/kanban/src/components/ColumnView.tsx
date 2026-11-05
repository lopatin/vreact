import { requires, callbackRequires, distinct, type int } from "vreact/spec";
import type { Card, ColumnId } from "../model";
import { CardView } from "./CardView";

type ColumnViewProps = {
  readonly col: ColumnId;
  readonly title: string;
  readonly cards: readonly Card[];
  readonly limit: int | null;
  readonly selected: int | null;
  readonly onMove: (id: int, to: ColumnId) => void;
  readonly onDelete: (id: int) => void;
  readonly onSelect: (id: int) => void;
};

/** A column: reports only ids of cards it shows; its cards need distinct ids (React keys). */
export function ColumnView(props: ColumnViewProps) {
  requires(distinct(props.cards, (c) => c.id));
  callbackRequires(props.onMove, (id, to) => props.cards.some((c) => c.id === id) && to !== props.col);
  callbackRequires(props.onDelete, (id) => props.cards.some((c) => c.id === id));
  callbackRequires(props.onSelect, (id) => props.cards.some((c) => c.id === id));
  const full = props.limit !== null && props.cards.length >= props.limit;
  return (
    <section className={full ? "column full" : "column"}>
      <h2>
        {props.title}{" "}
        <small>
          {props.cards.length}
          {props.limit !== null ? ` / ${props.limit}` : ""}
        </small>
      </h2>
      <ul>
        {props.cards.map((c) => (
          <CardView
            key={c.id}
            card={c}
            col={props.col}
            selected={props.selected === c.id}
            onMove={(id, to) => props.onMove(id, to)}
            onDelete={(id) => props.onDelete(id)}
            onSelect={(id) => props.onSelect(id)}
          />
        ))}
      </ul>
    </section>
  );
}
