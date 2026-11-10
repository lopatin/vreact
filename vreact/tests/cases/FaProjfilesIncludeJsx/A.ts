// expect: reject "include" lists src/App.jsx, which is not a VTS source
// A .jsx/.js source (allowJs) gets its types from JSDoc comments: `/** @type {T} */ (e)` is a
// cast the translator never sees. Listing one in "include" is an error of vreact.json.
import { int } from "vreact/spec";

export function one(): int {
  return 1;
}
