// The options chain: expiry buttons, expand/collapse all, the quick strike filter, the heat-map
// threshold, the watched strikes, one block per expiry (a term row and its strike rows), the
// order ticket and the working orders.
import { useReducer, useState } from "react";
import { requires, invariant, type int } from "vreact/spec";
import {
  type Expiry,
  type Ticket,
  type StrikeFilter,
  type Span,
  validChain,
  midPrice,
  atmIndex,
  strikeWindow,
  levelsOf,
  filterLabel,
  legFor,
  labelOf,
  contractText,
  marketOf,
  fmtPrice,
} from "./model";
import { chainReducer, wellFormed, INITIAL_UI, MAX_HEAT } from "./reducer";
import { byId } from "./collections";
import { TermRow } from "./TermRow";
import { StrikeRow } from "./StrikeRow";
import { OrderTicket } from "./OrderTicket";

const FILTERS: readonly StrikeFilter[] = ["s3", "s7", "s11", "s99", "all"];

export type OptionsChainProps = { readonly expiries: readonly Expiry[] };

export function OptionsChain(props: OptionsChainProps) {
  requires(validChain(props.expiries));
  const [ui, dispatch] = useReducer(chainReducer, INITIAL_UI);
  const [ticket, setTicket] = useState<Ticket | null>(null);
  invariant(wellFormed(ui));
  invariant(ticket === null || ticket.price > 0);

  const levels = levelsOf(ui.filter);
  // the ticket's expiry, looked up in the current props: it may have been delisted meanwhile
  const tExp = ticket === null ? undefined : byId(props.expiries, ticket.expiry);
  const allOpen = props.expiries.every((e) => !ui.collapsed.has(e.id));
  const ids = props.expiries.map((e) => e.id);

  return (
    <div className="chain">
      <div className="toolbar">
        <div className="expiries">
          {props.expiries.map((e) => (
            <a
              key={e.id}
              href={`#atm-${e.id}`}
              className={ui.focus === e.id ? "expiry on" : "expiry"}
              onClick={() => dispatch({ kind: "jump", expiry: e.id })}
            >
              {e.label}
            </a>
          ))}
        </div>
        <button onClick={() => dispatch({ kind: "collapse", ids: allOpen ? ids : [] })}>
          {allOpen ? "Collapse all" : "Expand all"}
        </button>
        <div className="filter">
          <span>Strikes ±</span>
          {FILTERS.map((f) => (
            <button key={filterLabel(f)} className={ui.filter === f ? "on" : ""} onClick={() => dispatch({ kind: "filter", filter: f })}>
              {filterLabel(f)}
            </button>
          ))}
        </div>
        <div className="heat">
          <span>Heat {ui.heat} ticks</span>
          <button disabled={ui.heat <= 1} onClick={() => dispatch({ kind: "heat", ticks: ui.heat - 1 })}>−</button>
          <button disabled={ui.heat >= MAX_HEAT} onClick={() => dispatch({ kind: "heat", ticks: ui.heat + 1 })}>+</button>
        </div>
        {ui.watch.size > 0 && (
          <div className="watching">
            <span>Watching</span>
            {[...ui.watch].toSorted((a, b) => a - b).map((k) => (
              <button key={k} className="chip" title="Stop watching" onClick={() => dispatch({ kind: "watch", strike: k })}>
                ★ {fmtPrice(k)}
              </button>
            ))}
          </div>
        )}
      </div>
      <table className="grid">
        <thead>
          <tr>
            <th colSpan={4}>Calls</th>
            <th>Strike</th>
            <th colSpan={4}>Puts</th>
            <th>Vol</th>
          </tr>
          <tr className="sub">
            <th>Qty</th>
            <th>Bid</th>
            <th>Ask</th>
            <th>Qty</th>
            <th></th>
            <th>Qty</th>
            <th>Bid</th>
            <th>Ask</th>
            <th>Qty</th>
            <th></th>
          </tr>
        </thead>
        {props.expiries.map((e) => {
          const live = midPrice(e.future);
          const held = ui.held.get(e.id) ?? null;
          const center: int | null = held === null ? live : held;
          const n = e.strikes.length;
          const atm = center === null ? -1 : atmIndex(e.strikes, center);
          // no ATM row (empty ladder, or no price at all) or "All": show every strike
          const span: Span = atm < 0 || levels === null ? { lo: 0, hi: n } : strikeWindow(n, atm, levels);
          // the filter's window, and the watched strikes: they are shown whatever the filter
          const rows = [...e.strikes.slice(span.lo, span.hi), ...e.strikes.filter((s) => ui.watch.has(s.strike))];
          const liveAtm = live === null ? -1 : atmIndex(e.strikes, live);
          const atmStrike = liveAtm < 0 ? null : e.strikes[liveAtm].strike;
          const open = !ui.collapsed.has(e.id);
          return (
            <tbody key={e.id}>
              <TermRow
                expiry={e}
                open={open}
                held={held}
                focused={ui.focus === e.id}
                onToggle={() => dispatch({ kind: "toggle", expiry: e.id })}
                onLock={() => {
                  if (held !== null) dispatch({ kind: "follow", expiry: e.id });
                  else if (live !== null) dispatch({ kind: "hold", expiry: e.id, price: live });
                }}
                onPick={(side, price) => {
                  if (price > 0) setTicket({ expiry: e.id, leg: "future", strike: 0, side: side, price: price });
                }}
              />
              {open &&
                rows.map((s) => (
                  <StrikeRow
                    key={s.strike}
                    strike={s}
                    price={live}
                    atm={s.strike === atmStrike}
                    anchor={s.strike === atmStrike ? `atm-${e.id}` : undefined}
                    heat={ui.heat}
                    watched={ui.watch.has(s.strike)}
                    onWatch={() => dispatch({ kind: "watch", strike: s.strike })}
                    onPick={(right, side, price) => {
                      if (price > 0) setTicket({ expiry: e.id, leg: legFor(right), strike: s.strike, side: side, price: price });
                    }}
                  />
                ))}
            </tbody>
          );
        })}
      </table>
      {ticket !== null && tExp !== undefined && (
        <OrderTicket
          key={`${ticket.expiry}/${ticket.leg}/${ticket.strike}/${ticket.side}/${ticket.price}`}
          ticket={ticket}
          title={`${tExp.symbol} ${tExp.label} ${contractText(ticket.leg, ticket.strike)}`}
          market={marketOf(tExp, ticket)}
          onSubmit={(qty, price) => {
            dispatch({ kind: "place", ticket: ticket, qty: qty, price: price });
            setTicket(null);
          }}
          onClose={() => setTicket(null)}
        />
      )}
      {ticket !== null && tExp === undefined && (
        <div className="ticket gone">
          <p>This contract is no longer listed.</p>
          <button onClick={() => setTicket(null)}>Close</button>
        </div>
      )}
      <section className="orders">
        <h3>Working orders</h3>
        {ui.orders.size === 0 ? (
          <p className="muted">None. Click a bid or an ask to open an order ticket.</p>
        ) : (
          <ul>
            {[...ui.orders].map(([id, o]) => (
              <li key={id}>
                <span className={o.buy ? "buy" : "sell"}>{o.buy ? "Buy" : "Sell"}</span> {o.qty} {labelOf(props.expiries, o.expiry)}{" "}
                {contractText(o.leg, o.strike)} @ {fmtPrice(o.price)}
                <button onClick={() => dispatch({ kind: "cancel", id: id })}>Cancel</button>
              </li>
            ))}
          </ul>
        )}
      </section>
    </div>
  );
}
