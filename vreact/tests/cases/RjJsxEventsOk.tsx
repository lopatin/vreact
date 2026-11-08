// expect: verified
// Accepted counterparts of the Rj rejections:
// * character references are decoded as JSX does (`type="butto&#110;"` is a plain button
//   input, so its onClick next to the form's onSubmit is fine; `&amp;`, `&#x41;` in text);
// * event fields copied into a const in the handler may be used by a functional update,
//   and array callbacks that run in place may read the event;
// * an effect may return its cleanup from a branch; what follows a nested `return` in a
//   branch still runs on the other path.
import { useState, useEffect } from "react";
import { invariant, type int } from "vreact/spec";

export function RjEntitiesOk() {
  const [n, setN] = useState<int>(0);
  const [m, setM] = useState<int>(0);
  invariant(n >= 0 && m >= 0);
  return (
    <form title="a &amp; b" onSubmit={(e) => { e.preventDefault(); setM(m + 1); }}>
      <p>x &amp; y &#x41;&#66; AT&T &lt;3</p>
      <input type="butto&#110;" value="&#43;1" onClick={() => setN(n + 1)} />
    </form>
  );
}

export function RjEventCopyOk(props: { readonly words: readonly string[] }) {
  const [s, setS] = useState<string>("");
  const [hits, setHits] = useState<int>(0);
  invariant(hits >= 0);
  return (
    <input value={s} onChange={(e) => {
      const v = e.target.value;
      setS((p) => (v === "" ? p : v));
      setHits(props.words.filter((w) => w === e.target.value).length);
    }} />
  );
}

export function RjCleanupBranchOk(props: { readonly on: boolean }) {
  const [n, setN] = useState<int>(0);
  invariant(n >= 0);
  useEffect(() => {
    if (props.on) {
      const msg = "on";
      return () => console.log(msg, n);
    }
    setN((k) => k + 1);
  }, [props.on, n]);
  // expression bodies whose value is undefined (no cleanup)
  useEffect(() => console.log("on", props.on), [props.on]);
  useEffect(() => setN((k) => k + 1), [props.on]);
  return <p>{n}</p>;
}
