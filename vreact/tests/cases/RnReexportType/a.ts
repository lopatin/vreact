// expect: reject error TS1205: Re-exporting a type when 'isolatedModules' is enabled requires using 'export type'
// A bundler compiles each file on its own (Vite: esbuild): it cannot know that Item is a type,
// keeps `export { Item }` and the import of Item, and the module fails to load (./types does not
// export Item). VTS checks every program with "isolatedModules" (formerly VERIFIED).
import { type int, ensures } from "vreact/spec";
import { Item, mk } from "./types";

export { Item };

export function f(x: int): int {
  ensures((r) => r === x);
  return mk(x).id;
}
