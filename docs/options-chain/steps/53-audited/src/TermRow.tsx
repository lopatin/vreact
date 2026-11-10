import { callbackRequires, type int } from "vreact/spec";
import { type Expiry, type Side, quotePrice, fmtPrice } from "./model";
import { PriceCell } from "./StrikeRow";

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
 */
export function TermRow(props: TermRowProps) {
  callbackRequires(props.onPick, (side, price) => quotePrice(props.expiry.future, side) === price);
  const f = props.expiry.future;
  const h = props.held;
  return (
    <tr className={props.focused ? "term focus" : "term"}>
      <td className="toggle">
        <button title={props.open ? "Hide strikes" : "Show strikes"} onClick={() => props.onToggle()}>
          {props.open ? "▾" : "▸"}
        </button>
      </td>
      <td className="name" colSpan={3}>
        {props.expiry.symbol} {props.expiry.label}
      </td>
      <td className="lock">
        <button
          className={h === null ? "locked" : "unlocked"}
          title={h === null ? "Locked to the futures price: click to hold the strike window here" : "Held: click to lock to the futures price"}
          onClick={() => props.onLock()}
        >
          {h === null ? "🔒" : "🔓"}
        </button>
      </td>
      <td className="qty">{f.bidQty}</td>
      <PriceCell price={f.bid} heat="none" itm={false} onPick={(x) => props.onPick("bid", x)} />
      <PriceCell price={f.ask} heat="none" itm={false} onPick={(x) => props.onPick("ask", x)} />
      <td className="qty">{f.askQty}</td>
      <td className="held">{h === null ? "live" : `held ${fmtPrice(h)}`}</td>
    </tr>
  );
}
