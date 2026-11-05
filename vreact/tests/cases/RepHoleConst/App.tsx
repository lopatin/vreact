// expect: status LIMIT=incomplete STEP=verified App=verified verdict=incomplete
// A hole() in a constant nothing uses still leaves the program unfinished (the module
// throws on import): every constant gets an axiom report, so this is INCOMPLETE, not VERIFIED.
import { hole, type int } from "vreact/spec";
export const LIMIT: int = hole<int>();
export const STEP: int = 2;
export function App() {
  return <p>hello</p>;
}
