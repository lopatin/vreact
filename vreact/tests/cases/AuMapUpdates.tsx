// expect: verified
// #58 r1: three handlers of the same shape (+1, +2, -1) updating one field through `map`, in one
// `render`: each handler is its own obligation with its own budget (the `-1` one used to exceed it).
import { useState } from "react";
import { invariant, distinct, type int } from "vreact/spec";

type Card = { readonly id: int; readonly title: string; readonly pts: int };

export function Points() {
  const [cards, setCards] = useState<readonly Card[]>([]);
  const [nextId, setNextId] = useState<int>(0);
  invariant(distinct(cards, (c) => c.id));
  invariant(cards.every((c) => c.id < nextId && 0 <= c.pts && c.pts <= 13));
  return (
    <ul>
      {cards.map((c) => (
        <li key={c.id}>
          <button onClick={() => setCards(cards.map((x) => (x.id === c.id && x.pts < 13 ? { ...x, pts: x.pts + 1 } : x)))}>+1</button>
          <button onClick={() => setCards(cards.map((x) => (x.id === c.id && x.pts < 12 ? { ...x, pts: x.pts + 2 } : x)))}>+2</button>
          <button onClick={() => setCards(cards.map((x) => (x.id === c.id && x.pts > 0 ? { ...x, pts: x.pts - 1 } : x)))}>-1</button>
        </li>
      ))}
    </ul>
  );
}
