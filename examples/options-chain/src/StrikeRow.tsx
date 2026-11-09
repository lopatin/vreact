import { requires, callbackRequires, type int } from "vreact/spec";
import { type Strike, type Right, type Side, type Heat, legOf, quotePrice, inTheMoney, heatOf, fmtPrice, fmtVol } from "./model";

export type PriceCellProps = {
  readonly price: int | null;
  readonly heat: Heat;
  readonly itm: boolean;
  readonly onPick: (price: int) => void;
};

/** One bid or ask cell. Clicking it reports exactly the price it shows; an empty cell has no button. */
export function PriceCell(props: PriceCellProps) {
  callbackRequires(props.onPick, (p) => props.price === p);
  const p = props.price;
  const cls = props.itm ? "px itm" : "px";
  if (p === null) return <td className={cls}>–</td>;
  return (
    <td className={`${cls} heat-${props.heat}`}>
      <button onClick={() => props.onPick(p)}>{fmtPrice(p)}</button>
    </td>
  );
}

export type StrikeRowProps = {
  readonly strike: Strike;
  readonly price: int | null; // live futures price, for in/out of the money
  readonly atm: boolean; // the at-the-money row
  readonly anchor: string | undefined; // element id the expiry button scrolls to
  readonly heat: int; // heat-map threshold, ticks
  readonly watched: boolean; // the strike is on the watch list
  readonly onPick: (right: Right, side: Side, price: int) => void;
  readonly onWatch: () => void;
};

/**
 * One strike: call market | strike (with its ☆ watch button) | put market | volatility.
 * Clicking a bid or an ask reports that cell's call/put, bid/ask and price. The contract checks
 * that every report is consistent (the price is the quote of the leg and side it names), not
 * which cell made it: that is the wiring below, like the column order.
 */
export function StrikeRow(props: StrikeRowProps) {
  requires(props.heat >= 1);
  callbackRequires(props.onPick, (right, side, price) => quotePrice(legOf(props.strike, right), side) === price);
  const s = props.strike;
  const t = props.heat;
  const p = props.price;
  const callItm = p !== null && inTheMoney("call", s.strike, p);
  const putItm = p !== null && inTheMoney("put", s.strike, p);
  const cq = callItm ? "qty itm" : "qty";
  const pq = putItm ? "qty itm" : "qty";
  return (
    <tr className={`${props.atm ? "row atm" : "row"}${props.watched ? " watched" : ""}`} id={props.anchor}>
      <td className={cq}>{s.call.bidQty}</td>
      <PriceCell price={s.call.bid} heat={heatOf("bid", s.call.bid, s.callTheo, t)} itm={callItm} onPick={(x) => props.onPick("call", "bid", x)} />
      <PriceCell price={s.call.ask} heat={heatOf("ask", s.call.ask, s.callTheo, t)} itm={callItm} onPick={(x) => props.onPick("call", "ask", x)} />
      <td className={cq}>{s.call.askQty}</td>
      <td className="strike">
        <button
          className={props.watched ? "watch on" : "watch"}
          title={props.watched ? "Stop watching this strike" : "Watch this strike: show it in every expiry, whatever the filter"}
          onClick={() => props.onWatch()}
        >
          {props.watched ? "★" : "☆"}
        </button>
        {fmtPrice(s.strike)}
      </td>
      <td className={pq}>{s.put.bidQty}</td>
      <PriceCell price={s.put.bid} heat={heatOf("bid", s.put.bid, s.putTheo, t)} itm={putItm} onPick={(x) => props.onPick("put", "bid", x)} />
      <PriceCell price={s.put.ask} heat={heatOf("ask", s.put.ask, s.putTheo, t)} itm={putItm} onPick={(x) => props.onPick("put", "ask", x)} />
      <td className={pq}>{s.put.askQty}</td>
      <td className="vol">{fmtVol(s.vol)}</td>
    </tr>
  );
}
