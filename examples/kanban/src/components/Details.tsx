import type { Card } from "../model";

type DetailsProps = { readonly card: Card; readonly onClose: () => void };

export function Details(props: DetailsProps) {
  return (
    <aside className="details">
      <h3>#{props.card.id} · {props.card.title}</h3>
      <p>{props.card.points} point estimate</p>
      <button onClick={() => props.onClose()}>Close</button>
    </aside>
  );
}
