// expect: reject only local `let` variables can be assigned
import { ensures, type int } from "vreact/spec";

type Doc = { title: ReadonlyMap<int, int> };

// A parameter named `document` is not the page: `document.title = …` assigns a field of the
// caller's object (VTS data is immutable), it is not the external write document.title = …
export function rename(document: Doc): int {
  ensures((r) => r === document.title.size);
  document.title = new Map<int, int>(document.title).set(1000, 1).set(1001, 2);
  return document.title.size;
}
