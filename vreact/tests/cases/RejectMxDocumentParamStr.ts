// expect: reject only local `let` variables can be assigned
import { ensures } from "vreact/spec";

type DocS = { title: string };

// a parameter named `document` with a string field `title`: assigning it mutates the caller's
// object (and the function returns the new title), so it cannot be taken for the external write
export function retitle(document: DocS): string {
  ensures((r) => r === document.title);
  document.title = "new";
  return document.title;
}
