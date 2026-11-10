import { requires, callbackRequires, type int } from "vreact/spec";
import { type Ticket, type Quote, validQty } from "./model";

export type OrderTicketProps = {
  readonly ticket: Ticket; // the clicked cell: contract, side, price
  readonly title: string;
  readonly market: Quote | null; // the contract's live market (null: strike no longer listed)
  readonly onSubmit: (qty: int, price: int) => void;
  readonly onClose: () => void;
};

/**
 * Order entry, pre-filled from a clicked cell. Submits only valid orders.
 * @trusted — stub: contract only, implementation pending
 */
export function OrderTicket(props: OrderTicketProps) {
  requires(props.ticket.price > 0);
  callbackRequires(props.onSubmit, (qty, price) => validQty(qty) && price > 0);
  return <div className="todo-stub">OrderTicket</div>;
}
