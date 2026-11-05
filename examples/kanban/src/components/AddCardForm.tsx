import { useState } from "react";
import { callbackRequires, invariant, type int } from "vreact/spec";
import { MAX_TITLE, MAX_POINTS, validTitle, validPoints } from "../model";

type AddCardFormProps = { readonly onAdd: (title: string, points: int) => void };

/** A controlled form. It only submits trimmed, non-empty titles and valid estimates. */
export function AddCardForm(props: AddCardFormProps) {
  callbackRequires(props.onAdd, (title, points) => validTitle(title) && validPoints(points));
  const [draft, setDraft] = useState<string>("");
  const [points, setPoints] = useState<int>(3);
  invariant(draft.length <= MAX_TITLE);
  invariant(validPoints(points));
  const title = draft.trim();
  return (
    <form
      className="add"
      onSubmit={(e) => {
        e.preventDefault();
        if (title.length === 0) return;
        props.onAdd(title, points);
        setDraft("");
      }}
    >
      <input
        value={draft}
        placeholder="New card…"
        onChange={(e) => {
          if (e.target.value.length <= MAX_TITLE) setDraft(e.target.value);
        }}
      />
      <button type="button" disabled={points <= 1} onClick={() => { if (points > 1) setPoints(points - 1); }}>−</button>
      <span className="points">{points} pt</span>
      <button type="button" disabled={points >= MAX_POINTS} onClick={() => { if (points < MAX_POINTS) setPoints(points + 1); }}>+</button>
      <button type="submit" disabled={title.length === 0}>Add</button>
    </form>
  );
}
