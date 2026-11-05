import { useReducer } from "react";
import { invariant, type int } from "vreact/spec";
import { type Line, wellFormed } from "./model";
import { reducer } from "./reducer";
import { LineRow } from "./LineRow";

const PRODUCTS: readonly int[] = [1, 2, 3];
const EMPTY: readonly Line[] = [];

export function App() {
  const [lines, dispatch] = useReducer(reducer, EMPTY);
  invariant(wellFormed(lines));
  const count = lines.reduce((s: int, l: Line) => s + l.qty, 0);
  return (
    <div className="cart">
      {PRODUCTS.map((p) => (
        <button key={p} onClick={() => dispatch({ kind: "add", id: p })}>
          Add product {p}
        </button>
      ))}
      <ul>
        {lines.map((l) => (
          <LineRow
            key={l.id}
            line={l}
            onInc={(id) => dispatch({ kind: "inc", id })}
            onDec={(id) => dispatch({ kind: "dec", id })}
            onRemove={(id) => dispatch({ kind: "remove", id })}
          />
        ))}
      </ul>
      <p>{count} item(s) in the cart</p>
    </div>
  );
}
