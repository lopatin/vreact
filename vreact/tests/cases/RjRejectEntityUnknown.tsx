// expect: reject the character reference &check; is not an HTML 4 entity
// Entity names outside the HTML 4 table are left as text by TypeScript and Babel, but other
// compilers may know them: rejected (also in JSX text).
export function RjEntityUnknown() {
  return <p>done &check;</p>;
}
