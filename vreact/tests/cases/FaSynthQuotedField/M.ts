// expect: synth size=3 get=- set={~...p,~"my-field":~v~} out=scope:~p,~p.other noout=p.my-field
// names-r1-6: synth read every field as `p.<name>`, also "my-field", whose `p.my-field` means
// `p.my - field` in JS (and VTS rejects `p["my-field"]`): the scope listed it and every candidate
// built from it threw. Such a field is not read; in an object literal its key is quoted.
import { ensures, hole, type int } from "vreact/spec";
import { fieldOf, type R } from "./lib";

export function get(p: R): int {
  ensures((r) => r === fieldOf(p));
  return hole<int>();
}

export function set(p: R, v: int): R {
  ensures((r) => fieldOf(r) === v && r.other === p.other);
  return hole<R>();
}
