// expect: verified
// Layouts that stay within one discrete handler per click in Chromium 152 (react-dom
// 18.3.1, one programmatic click each) and in jsdom: inside a submit button, a checkbox,
// a radio button and a link handle their own click (no DOMActivate reaches the button);
// inside a label, a click on interactive content — and on anything inside it: a link's
// span, a button's span, a details' summary, a select's option — is not re-dispatched;
// a label around (or naming) a submit/reset control submits/resets once.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function A() {
  const [n, setN] = useState<int>(0);
  invariant(0 <= n && n <= 1);
  return (
    <div>
      <form onSubmit={(e) => { e.preventDefault(); if (n < 1) setN((m) => m + 1); }}>
        <button>
          <input type="checkbox" onClick={() => { if (n < 1) setN((m) => m + 1); }} />
          <input type="radio" onClick={() => { if (n < 1) setN((m) => m + 1); }} />
          <a href="#more" onClick={() => { if (n < 1) setN((m) => m + 1); }}>more</a>
          go
        </button>
      </form>
      <label htmlFor="c1"><a href="#y"><span onClick={() => { if (n < 1) setN((m) => m + 1); }}>link</span></a></label>
      <input id="c1" type="checkbox" onClick={() => { if (n < 1) setN((m) => m + 1); }} />
      <label htmlFor="c2"><button type="button"><span onClick={() => { if (n < 1) setN((m) => m + 1); }}>button</span></button></label>
      <input id="c2" type="checkbox" onClick={() => { if (n < 1) setN((m) => m + 1); }} />
      <label htmlFor="c3"><details><summary><span onClick={() => { if (n < 1) setN((m) => m + 1); }}>details</span></summary></details></label>
      <input id="c3" type="checkbox" onClick={() => { if (n < 1) setN((m) => m + 1); }} />
      <label htmlFor="c4"><select><option onClick={() => { if (n < 1) setN((m) => m + 1); }}>option</option></select></label>
      <input id="c4" type="checkbox" onClick={() => { if (n < 1) setN((m) => m + 1); }} />
      <form onSubmit={() => { if (n < 1) setN((m) => m + 1); }}>
        <label>Go <input type="submit" /></label>
      </form>
      <form onSubmit={() => { if (n < 1) setN((m) => m + 1); }}>
        <label>Go <button>go</button></label>
      </form>
      <form onReset={() => { if (n < 1) setN((m) => m + 1); }}>
        <label>Reset <input type="reset" /></label>
      </form>
      <form onSubmit={() => { if (n < 1) setN((m) => m + 1); }}>
        <label htmlFor="b1">Send</label>
        <button id="b1">send</button>
      </form>
    </div>
  );
}
