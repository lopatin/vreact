// expect: verified RnProtoNamesOk_f=verified
// Required fields named like Object.prototype's members are own properties of every value of
// the type (TypeScript requires them in each literal): accepted.
import { type int, ensures } from "vreact/spec";

type Team = { readonly constructor: string; readonly toString: int; readonly valueOf: int | undefined };

export function RnProtoNamesOk_f(t: Team): int {
  ensures((r) => r === t.toString + (t.valueOf === undefined ? 0 : t.valueOf));
  return t.toString + (t.valueOf === undefined ? 0 : t.valueOf);
}

export function RnProtoNamesOk_g(): int {
  ensures((r) => r === 3);
  const t: Team = { constructor: "Ferrari", toString: 3, valueOf: undefined };
  return RnProtoNamesOk_f(t);
}
