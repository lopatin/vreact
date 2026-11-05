import { callbackRequires, type int } from "vreact/spec";
import { type Expiry, type Side, quotePrice } from "./model";

export type TermRowProps = {
  readonly expiry: Expiry;
  readonly open: boolean; // strikes shown
  readonly held: int | null; // price the window is held at; null = locked to the futures price
  readonly focused: boolean;
  readonly onToggle: () => void;
  readonly onLock: () => void;
  readonly onPick: (side: Side, price: int) => void;
};

/**
 * The term row of an expiry: symbol and expiry, the futures market, the lock, expand/collapse.
 * It only ever reports a price of the futures market it shows.
 * @trusted — stub: contract only, implementation pending
 */
export function TermRow(props: TermRowProps) {
  callbackRequires(props.onPick, (side, price) => quotePrice(props.expiry.future, side) === price);
  return (
    <tr className="todo-stub">
      <td>TermRow</td>
    </tr>
  );
}
