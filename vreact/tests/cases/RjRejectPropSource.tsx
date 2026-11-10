// expect: reject a prop named __source
// React 18 removes key, ref, __self and __source from the props of every element
// (RESERVED_PROPS in React.createElement and react/jsx-runtime): Label never receives
// __source, so `props.__source.length` throws a TypeError while rendering.
function Label(props: { readonly __source: string }) {
  return <p>{props.__source.length}</p>;
}
export function RjPropSource() {
  return <Label __source="abc" />;
}
