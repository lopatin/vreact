// expect: reject `declare global`, `declare module` and namespaces are not supported
// Augmenting React's types in a verified source (module augmentation).
import "react";
import { type int } from "vreact/spec";

declare module "react" {
  interface ButtonHTMLAttributes<T> {
    commandfor?: string;
  }
}

export function n(x: int): int {
  return x;
}
