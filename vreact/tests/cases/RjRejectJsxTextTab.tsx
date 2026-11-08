// expect: reject JSX compilers do not agree on this text
// A tab inside JSX text stays a tab with TypeScript's JSX transform, but Babel turns it into a
// space: the rendered text would depend on the compiler.
export function RjJsxTextTab() {
  return <p>a	b</p>;
}
