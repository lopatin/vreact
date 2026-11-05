// The invoker attributes (HTML commandfor / command), not in @types/react 18.
import "react";
declare module "react" {
  interface ButtonHTMLAttributes<T> {
    commandfor?: string;
    command?: string;
  }
}
