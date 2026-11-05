// expect: verified
// Many invariant conjuncts preserved by a guarded map-update (formerly timed out).
import { useState } from "react";
import { invariant, requires, ensures, distinct, type int } from "vreact/spec";

type Card = { readonly id: int; readonly title: string; readonly pts: int };

export function bump(xs: readonly Card[], id: int, nextId: int): readonly Card[] {
  requires(distinct(xs, (c) => c.id) && xs.every((c) => 0 <= c.pts && c.pts <= 13 && c.id < nextId && c.title.length > 0));
  ensures((r: readonly Card[]) => distinct(r, (c) => c.id) && r.every((c) => 0 <= c.pts && c.pts <= 13 && c.id < nextId && c.title.length > 0));
  return xs.map((c) => (c.id === id && c.pts < 13 ? { ...c, pts: c.pts + 1 } : c));
}

export function LnEstimates() {
  const [cards, setCards] = useState<readonly Card[]>([]);
  const [nextId, setNextId] = useState<int>(0);
  invariant(distinct(cards, (c) => c.id));
  invariant(cards.every((c) => c.id < nextId && c.title.length > 0 && 0 <= c.pts && c.pts <= 13));
  return (
    <div>
      <button onClick={() => { setCards([...cards, { id: nextId, title: "new", pts: 0 }]); setNextId(nextId + 1); }}>add</button>
      <ul>
        {cards.map((c) => (
          <li key={c.id}>
            <button onClick={() => setCards(cards.map((x) => (x.id === c.id && x.pts < 13 ? { ...x, pts: x.pts + 1 } : x)))}>+</button>
          </li>
        ))}
      </ul>
    </div>
  );
}
