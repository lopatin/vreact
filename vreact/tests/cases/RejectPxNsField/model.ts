// expect: reject Lean name clash: the module src/model/todo.ts has the Lean namespace VTS.model.todo, which src/model.ts already uses for its declaration `todo` (both generate the Lean name VTS.model.todo.title)
// The field title of the type todo is the Lean projection VTS.model.todo.title; the module
// src/model/todo.ts (namespace VTS.model.todo) declares title too: a real clash of the names
// Lean derives from a structure.
import { type int } from "vreact/spec";
export type todo = { readonly title: int; readonly done: boolean };
