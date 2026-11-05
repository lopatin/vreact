// expect: reject Lean name clash: the module src/model/range.ts has the Lean namespace VTS.model.range, which src/model.ts already uses for its declaration `range` (whose member VTS.model.range.max Lean would find instead of its own `max`
// Nested namespaces are allowed (see PxNsNested), but here the field max of the type range is
// VTS.model.range.max, and the module src/model/range.ts (namespace VTS.model.range) uses
// Lean's max (Math.max) unqualified: Lean would take the field instead (a type error in the
// generated Lean). Rejected with a rename hint.
import { type int } from "vreact/spec";
export type range = { readonly min: int; readonly max: int };
