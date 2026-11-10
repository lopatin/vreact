// expect: reject is part of the TypeScript program (through a `/// <reference>`, an import or the tsconfig) but is not a VTS source
/// <reference path="./globals.d.ts" />
// A declaration file of the project augments the global Array type (here with a member the
// translation does not model, but it could as well add overloads to modelled ones): only
// TypeScript's and installed libraries may declare what library code means.
import { type int } from "vreact/spec";

export function first(xs: readonly int[]): int {
  return xs.length;
}
