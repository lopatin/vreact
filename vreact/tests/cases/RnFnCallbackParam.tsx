// expect: reject parameter f of callback onPick has the function type () => void, which is not data
// A callback prop passing a function (formerly an internal error).
export function RnFnCallbackParam(props: { readonly onPick: (f: () => void) => void }) {
  return <p>x</p>;
}
