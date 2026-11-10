// expect: fail index sortedAt=incomplete allHeads=incomplete someHead=incomplete
// A quantifier body inside a contract that runs is called by JS for its bounds / elements, and
// implies inside it still evaluates both arguments: sortedAt([{ v: 1 }]) reads xs[-1].v at i = 0,
// allHeads([[]]) and someHead([[]]) read [][0].v — each throws a TypeError. The body may assume
// its bounds or membership (JS calls it only there), not the antecedent of implies.
import { requires, implies, forall, exists, type int } from "vreact/spec";

type Item = { readonly v: int };

export function sortedAt(xs: readonly Item[]): boolean {
  requires(forall(0, xs.length, (i) => implies(i > 0, xs[i - 1].v <= xs[i].v)));
  return true;
}

export function allHeads(rows: readonly (readonly Item[])[]): boolean {
  requires(rows.every((r) => implies(r.length > 0, r[0].v >= 0)));
  return true;
}

export function someHead(rows: readonly (readonly Item[])[]): boolean {
  requires(exists(0, rows.length, (i) => implies(rows[i].length > 0, rows[i][0].v >= 0)));
  return true;
}
