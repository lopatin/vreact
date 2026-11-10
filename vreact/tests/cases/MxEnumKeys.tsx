// expect: verified
import { type int } from "vreact/spec";

// string-literal enum members are valid React keys (their strings); an enum-keyed Map renders by its keys
export type MxekStatus = "todo" | "doing" | "done";

const MXEK_STATUSES: readonly MxekStatus[] = ["todo", "doing", "done"];

export function MxekCols() {
  return (
    <div>
      {MXEK_STATUSES.map((s) => (
        <section key={s}>{s}</section>
      ))}
    </div>
  );
}

export function MxEnumKeys(props: { readonly counts: ReadonlyMap<MxekStatus, int> }) {
  return (
    <ul>
      {[...props.counts].map(([s, n]) => (
        <li key={s}>
          {s}: {n}
        </li>
      ))}
      {[...props.counts.keys()].map((s) => (
        <li key={s}>{s}</li>
      ))}
    </ul>
  );
}
