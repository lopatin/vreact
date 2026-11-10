// expect: fail callback-contract faildesc=through~the~local~pick
// The contract stated on a renamed destructured callback (`pick` holds props.onPick) is checked
// at every call and forward made through the local: pick(-1), and forwarding pick to a child
// that promises nothing about its argument. (It used to be rejected.)
import { callbackRequires, type int } from "vreact/spec";

type CP = { readonly onPick: (i: int) => void };
type GP = { readonly onA: (i: int) => void };
export function C({ onPick: pick }: CP) {
  callbackRequires(pick, (i) => i >= 0);
  return (
    <div>
      <button onClick={() => pick(-1)}>c</button>
      <G onA={pick} />
    </div>
  );
}

export function G(props: GP) {
  return <button onClick={() => props.onA(-3)}>g</button>;
}
