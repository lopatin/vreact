// expect: reject through the module namespace `L`: VTS reads a component tag only as a plain name
// `<L.Row/>` (a component through a namespace import) is rejected with the restriction itself,
// not as a "dynamic element type".
import * as L from "./lib";

export function App() {
  return <div><L.Row /></div>;
}
