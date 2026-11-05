import { requires, callbackRequires, type int } from "vreact/spec";
import { type Strike, type Right, type Side, legOf, quotePrice } from "./model";

export type StrikeRowProps = {
  readonly strike: Strike;
  readonly price: int | null; // live futures price, for in/out of the money
  readonly atm: boolean; // the at-the-money row
  readonly anchor: string | null; // element id the expiry button scrolls to
  readonly heat: int; // heat-map threshold, ticks
  readonly onPick: (right: Right, side: Side, price: int) => void;
};

/**
 * One strike: call market | strike | put market | volatility.
 * Clicking a bid or an ask reports exactly the price shown in that cell.
 * @trusted — stub: contract only, implementation pending
 */
export function StrikeRow(props: StrikeRowProps) {
  requires(props.heat >= 1);
  callbackRequires(props.onPick, (right, side, price) => quotePrice(legOf(props.strike, right), side) === price);
  return (
    <tr className="todo-stub">
      <td>StrikeRow</td>
    </tr>
  );
}
