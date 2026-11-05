import { type int } from "vreact/spec";

export type Todo = { readonly id: int; readonly text: string; readonly done: boolean };
export type Filter = "all" | "active" | "done";
