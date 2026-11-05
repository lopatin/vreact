// expect: fail handler TrOr3Ok=verified TrOr3Bad=incomplete
// `s.kind === "editing" || s.n > 0` on a 3-variant union: the right operand sees the two
// other variants (both with n), in invariants, render and functions.
import { useState } from "react";
import { invariant, ensures, type int } from "vreact/spec";

type Status = { readonly kind: "editing" } | { readonly kind: "sent"; readonly n: int } | { readonly kind: "failed"; readonly n: int };

export function count(s: Status): int {
  ensures((r: int) => s.kind === "editing" || r === s.n);
  if (s.kind === "editing") return 0;
  return s.n;
}

export function TrOr3Ok() {
  const [status, setStatus] = useState<Status>({ kind: "editing" });
  invariant(status.kind === "editing" || status.n > 0);
  return (
    <div>
      <p>{status.kind !== "editing" ? status.n : 0}</p>
      <button onClick={() => setStatus({ kind: "sent", n: 1 })}>send</button>
      <button onClick={() => setStatus(status.kind === "editing" ? { kind: "failed", n: 2 } : { kind: "failed", n: status.n })}>fail</button>
    </div>
  );
}

export function TrOr3Bad() {
  const [status, setStatus] = useState<Status>({ kind: "editing" });
  invariant(status.kind === "editing" || status.n > 0);
  return <button onClick={() => setStatus({ kind: "failed", n: 0 })}>{status.kind}</button>;
}
