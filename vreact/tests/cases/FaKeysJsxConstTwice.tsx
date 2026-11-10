// expect: reject two children of <ul> have the same key "row"
// A JSX const rendered twice in one children array is two children with its key.
export function Twice() {
  const row = <li key="row">x</li>;
  return (
    <ul>
      {row}
      {row}
    </ul>
  );
}
