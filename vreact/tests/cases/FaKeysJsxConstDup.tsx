// expect: fail unique-keys ConstTwice=incomplete LetKey=incomplete faildesc=keys~of~the~children~of~
// A JSX const keyed by an expression: rendered twice, it is two children with one key; its key
// is the value at the declaration, where JS evaluates the element (LetKey's row has the key "a"
// although k is "b" where it is rendered, so it collides with the literal "a").
export function ConstTwice(props: { readonly k: string }) {
  const row = <li key={props.k}>x</li>;
  return (
    <ul>
      {row}
      {row}
    </ul>
  );
}
export function LetKey() {
  let k: string = "a";
  const row = <p key={k}>x</p>;
  k = "b";
  return (
    <div>
      {row}
      <p key="a">y</p>
    </div>
  );
}
