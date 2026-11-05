import { useState } from "react";
import { requires, callbackRequires, invariant, type int } from "vreact/spec";
import { type Ticket, type Quote, validQty, MAX_QTY, crosses, quoteText, fmtPrice } from "./model";

export type OrderTicketProps = {
  readonly ticket: Ticket; // the clicked cell: contract, side, price
  readonly title: string;
  readonly market: Quote | null; // the contract's live market (null: strike no longer listed)
  readonly onSubmit: (qty: int, price: int) => void;
  readonly onClose: () => void;
};

const LOTS: readonly int[] = [1, 5, 10, 25];

/**
 * Order entry, pre-filled from a clicked cell: clicking a bid prepares a sell at the bid,
 * clicking an ask a buy at the ask. Submits only valid orders.
 */
export function OrderTicket(props: OrderTicketProps) {
  requires(props.ticket.price > 0);
  callbackRequires(props.onSubmit, (qty, price) => validQty(qty) && price > 0);
  const [qty, setQty] = useState<int>(1);
  const [price, setPrice] = useState<int>(props.ticket.price);
  invariant(validQty(qty) && price > 0);
  const buy = props.ticket.side === "ask";
  const m = props.market;
  const marketable = m !== null && crosses(buy, price, m);
  return (
    <div className={buy ? "ticket buy" : "ticket sell"}>
      <h3>
        {buy ? "Buy" : "Sell"} {props.title}
      </h3>
      <div className="field">
        <span>Quantity</span>
        <button disabled={qty <= 1} onClick={() => { if (qty > 1) setQty(qty - 1); }}>−</button>
        <b>{qty}</b>
        <button disabled={qty >= MAX_QTY} onClick={() => { if (qty < MAX_QTY) setQty(qty + 1); }}>+</button>
        {LOTS.map((n) => (
          <button key={n} className={qty === n ? "lot on" : "lot"} onClick={() => setQty(n)}>
            {n}
          </button>
        ))}
      </div>
      <div className="field">
        <span>Price</span>
        <button disabled={price <= 1} onClick={() => { if (price > 1) setPrice(price - 1); }}>−</button>
        <b>{fmtPrice(price)}</b>
        <button onClick={() => setPrice(price + 1)}>+</button>
      </div>
      <p className="market">Market {m === null ? "not listed" : quoteText(m)}</p>
      {marketable && <p className="warn">Marketable: this order would trade at once.</p>}
      <div className="actions">
        <button className="submit" onClick={() => props.onSubmit(qty, price)}>
          Submit
        </button>
        <button onClick={() => props.onClose()}>Cancel</button>
      </div>
    </div>
  );
}
