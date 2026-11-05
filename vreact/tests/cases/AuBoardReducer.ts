// expect: verified
// #58 p1-board: an 8-case reducer whose postcondition keeps a 4-conjunct invariant (distinct ids
// across three columns, field bounds, a WIP limit, a nullable selection) — 36 cases after
// splitting. It used to run out of the default per-obligation budget (about 1.1M heartbeats):
// `vreact_finish` ran its expensive `simp_all` fallbacks at every level of the invariant's
// conjunction before trying the conjuncts.
import { ensures, implies, distinct, type int } from "vreact/spec";

export type Card = { readonly id: int; readonly title: string; readonly pts: int };
export type Col = "todo" | "doing" | "done";
export type Board = {
  readonly todo: readonly Card[];
  readonly doing: readonly Card[];
  readonly done: readonly Card[];
  readonly nextId: int;
  readonly selected: int | null;
};
export type Act =
  | { readonly kind: "add"; readonly title: string }
  | { readonly kind: "del"; readonly id: int }
  | { readonly kind: "move"; readonly id: int; readonly to: Col }
  | { readonly kind: "select"; readonly id: int }
  | { readonly kind: "deselect" }
  | { readonly kind: "rename"; readonly id: int; readonly title: string }
  | { readonly kind: "bump"; readonly id: int }
  | { readonly kind: "clearDone" };

export function all(b: Board): readonly Card[] {
  return [...b.todo, ...b.doing, ...b.done];
}

export function wf(b: Board): boolean {
  return (
    distinct(all(b), (c) => c.id) &&
    all(b).every((c) => c.id < b.nextId && c.title.length > 0 && 0 <= c.pts && c.pts <= 13) &&
    b.doing.length <= 3 &&
    (b.selected === null || all(b).some((c) => c.id === b.selected))
  );
}

export function reducer(b: Board, a: Act): Board {
  ensures((r: Board) => implies(wf(b), wf(r)));
  switch (a.kind) {
    case "add": {
      const t = a.title.trim();
      if (t.length === 0) return b;
      return { ...b, todo: [...b.todo, { id: b.nextId, title: t, pts: 0 }], nextId: b.nextId + 1 };
    }
    case "del": {
      const sel = b.selected === a.id ? null : b.selected;
      return {
        ...b,
        todo: b.todo.filter((c) => c.id !== a.id),
        doing: b.doing.filter((c) => c.id !== a.id),
        done: b.done.filter((c) => c.id !== a.id),
        selected: sel,
      };
    }
    case "move": {
      const c = all(b).find((x) => x.id === a.id);
      if (c === undefined) return b;
      const rest: Board = {
        ...b,
        todo: b.todo.filter((x) => x.id !== a.id),
        doing: b.doing.filter((x) => x.id !== a.id),
        done: b.done.filter((x) => x.id !== a.id),
      };
      if (a.to === "todo") return { ...rest, todo: [...rest.todo, c] };
      if (a.to === "doing") {
        if (rest.doing.length >= 3) return b;
        return { ...rest, doing: [...rest.doing, c] };
      }
      return { ...rest, done: [...rest.done, c] };
    }
    case "select":
      if (!all(b).some((c) => c.id === a.id)) return b;
      return { ...b, selected: a.id };
    case "deselect":
      return { ...b, selected: null };
    case "rename": {
      const t = a.title.trim();
      if (t.length === 0) return b;
      return {
        ...b,
        todo: b.todo.map((c) => (c.id === a.id ? { ...c, title: t } : c)),
        doing: b.doing.map((c) => (c.id === a.id ? { ...c, title: t } : c)),
        done: b.done.map((c) => (c.id === a.id ? { ...c, title: t } : c)),
      };
    }
    case "bump":
      return {
        ...b,
        todo: b.todo.map((c) => (c.id === a.id && c.pts < 13 ? { ...c, pts: c.pts + 1 } : c)),
      };
    case "clearDone": {
      const sel = b.selected !== null && b.done.some((c) => c.id === b.selected) ? null : b.selected;
      return { ...b, done: [], selected: sel };
    }
  }
}
