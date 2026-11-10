// expect: reject srcDoc is a document whose scripts run with access to this page
// Sibling of RjRejectJavascriptUrl: the frame of a srcDoc has this page's origin, so its script
// can change the DOM React manages (parent.document): code outside the verified program.
import { useState } from "react";
import { type int } from "vreact/spec";

export function RjSrcDoc() {
  const [n, setN] = useState<int>(0);
  return (
    <div>
      <button onClick={() => setN(n + 1)}>{n}</button>
      <iframe title="x" srcDoc="<script>parent.document.body.textContent = ''</script>" />
    </div>
  );
}
