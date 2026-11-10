// expect: verified
// #48: `includes`/`startsWith`/`endsWith` of literal strings are decided (a simproc on the code
// units), e.g. a handler that stores a literal address under the invariant `to.includes("@")`.
import { useState } from "react";
import { invariant, ensures } from "vreact/spec";

type Status = { readonly kind: "editing" } | { readonly kind: "sent"; readonly to: string };

export function Demo() {
  const [status, setStatus] = useState<Status>({ kind: "editing" });
  invariant(status.kind === "editing" || status.to.includes("@"));
  return (
    <div>
      <button onClick={() => setStatus({ kind: "sent", to: "a@b" })}>demo</button>
      <button onClick={() => setStatus({ kind: "editing" })}>reset</button>
    </div>
  );
}

export function lits(): boolean {
  ensures((r: boolean) => r === true);
  return "a@b".includes("@") && !"ab".includes("@") && "hello".startsWith("he") && "hello".endsWith("lo") &&
    !"hello".endsWith("he") && "".includes("") && "😀x".includes("x");
}
