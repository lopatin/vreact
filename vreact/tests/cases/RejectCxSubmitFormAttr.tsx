// expect: reject form=… names its form
// <button form="f"> submits the form with id "f" wherever it is (here a sibling, possibly
// another component): its onClick and that form's onSubmit run in one batch.
import { useState } from "react";
import { invariant, type int } from "vreact/spec";
export function A() {
  const [n, setN] = useState<int>(0);
  invariant(0 <= n && n <= 1);
  return (
    <div>
      <form id="f" onSubmit={(e) => { e.preventDefault(); if (n < 1) setN((m) => m + 1); }}></form>
      <button form="f" onClick={() => { if (n < 1) setN((m) => m + 1); }}>go</button>
    </div>
  );
}
