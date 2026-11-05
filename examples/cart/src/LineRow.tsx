import { requires, callbackRequires, type int } from "vreact/spec";
import { type Line, MAX_QTY } from "./model";

type LineRowProps = {
  readonly line: Line;
  readonly onInc: (id: int) => void;
  readonly onDec: (id: int) => void;
  readonly onRemove: (id: int) => void;
};

/** One cart line. It only ever reports its own product id. */
export function LineRow(props: LineRowProps) {
  requires(1 <= props.line.qty && props.line.qty <= MAX_QTY);
  callbackRequires(props.onInc, (id) => id === props.line.id);
  callbackRequires(props.onDec, (id) => id === props.line.id);
  callbackRequires(props.onRemove, (id) => id === props.line.id);
  return (
    <li>
      Product {props.line.id}: {props.line.qty}
      <button disabled={props.line.qty <= 1} onClick={() => props.onDec(props.line.id)}>−</button>
      <button disabled={props.line.qty >= MAX_QTY} onClick={() => props.onInc(props.line.id)}>+</button>
      <button onClick={() => props.onRemove(props.line.id)}>Remove</button>
    </li>
  );
}
