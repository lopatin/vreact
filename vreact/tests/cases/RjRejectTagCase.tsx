// expect: reject an HTML document lower-cases element names, so it is a <foreignobject>
// Outside <svg> a tag is an HTML element, whose name the document lower-cases: the checks,
// which compare tag names, must see the element the document creates, so a name with
// upper-case letters (here an SVG element name used outside <svg>) is rejected.
import { useState } from "react";
import { type int } from "vreact/spec";

export function RjTagCase() {
  const [n, setN] = useState<int>(0);
  return (
    <div>
      <foreignObject>
        <button type="button" onClick={() => setN(n + 1)}>{n}</button>
      </foreignObject>
    </div>
  );
}
