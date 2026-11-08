// expect: verified
// Lib and React type names are recognised by their declaration: project types spelled
// `ReactNode` or `ReadonlyArray` are the project's (formerly the spelling `ReactNode` meant
// React's node type), React's ReactNode under an alias (`Node`) is React's node type (formerly
// read through React's own declaration: an error inside @types/react), and a type with a React
// node field that nothing uses as data no longer stops the translation.
import type { ReactNode as Node } from "react";
import { type int, ensures } from "vreact/spec";

type ReactNode = int;
interface ReadonlyArray {
  readonly n: int;
}
type Slot = { readonly title: string; readonly body: Node };

export function f(x: ReactNode, y: ReadonlyArray): ReactNode {
  ensures((r) => r === x + y.n);
  return x + y.n;
}

export function RnTypeNames(): JSX.Element {
  return <p>{f(1, { n: 2 })}</p>;
}
