// expect: reject two children of <>…</> have the same key "a"
// A fragment's children are one array too (the root of a component, here).
export function Frag() {
  return (
    <>
      <p key="a">one</p>
      <b>between</b>
      <p key="a">two</p>
    </>
  );
}
