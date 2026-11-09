// expect: fail unique-keys
// wrong: the same enum member twice gives two equal React keys

export type MxekdStatus = "todo" | "doing" | "done";

const MXEKD_STATUSES: readonly MxekdStatus[] = ["todo", "doing", "todo"];

export function MxEnumKeysDup() {
  return (
    <div>
      {MXEKD_STATUSES.map((s) => (
        <section key={s}>{s}</section>
      ))}
    </div>
  );
}
