// expect: verified
// Complement narrowing of discriminated unions: else branch, early return, `||`, ternary
// false branch (two variants), and the remaining variants after exclusions (three variants).
import { useState } from "react";
import { invariant, ensures, type int } from "vreact/spec";

type Status = { readonly kind: "editing" } | { readonly kind: "sent"; readonly to: string };
type Three = { readonly kind: "a" } | { readonly kind: "b"; readonly x: int } | { readonly kind: "c"; readonly x: int; readonly y: int };
type Data = { readonly kind: "loading" } | { readonly kind: "ready"; readonly text: string };

export function ctlLabelRet(s: Status): string {
  if (s.kind === "editing") return "draft";
  return s.to;
}

export function ctlLabelElse(s: Status): string {
  if (s.kind === "editing") {
    return "draft";
  } else {
    return s.to;
  }
}

export function ctlLabelTern(s: Status): string {
  return s.kind === "editing" ? "draft" : s.to;
}

export function ctlOk(s: Status): boolean {
  return s.kind === "editing" || s.to.length > 0;
}

export function ctlExcl(t: Three): int {
  ensures((r: int) => r >= 0 || t.kind === "c");
  if (t.kind === "a") return 0;
  if (t.kind === "b") return 1;
  return t.y;
}

export function ctlShared(t: Three): int {
  if (t.kind === "a") return 0;
  return t.x;
}

export function CtlRemote() {
  const [d, setD] = useState<Data>({ kind: "loading" });
  invariant(d.kind === "loading" || d.text.length <= 10);
  if (d.kind === "loading") return <button onClick={() => setD({ kind: "ready", text: "hi" })}>load</button>;
  return <p>{d.text}</p>;
}
