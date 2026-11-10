// expect: reject a javascript: URL runs its code in the page when it is followed
// Following the link runs its code in the page (React 18 warns, but sets the URL): code outside
// the verified program. The URL parser drops the leading space and the tab, and the scheme is
// ASCII-case-insensitive.
import { useState } from "react";
import { type int } from "vreact/spec";

export function RjJavascriptUrl() {
  const [n, setN] = useState<int>(0);
  return (
    <div>
      <button onClick={() => setN(n + 1)}>{n}</button>
      <a href=" Java&#9;Script:document.body.textContent=''">clear</a>
    </div>
  );
}
