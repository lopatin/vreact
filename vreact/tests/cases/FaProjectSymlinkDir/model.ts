// expect: reject src/w is a symbolic link (to .shared/lib): symbolic links in the source directory are not supported
// src/w is a link to src/.shared/lib (a directory vreact skips). TypeScript resolves "../model" of
// src/w/Counter.tsx from the link's path: src/model.ts (LIMIT = 3); Vite from the real path
// src/.shared/lib/: src/.shared/model.ts (LIMIT = 100), and the invariant breaks.
import { type int } from "vreact/spec";
export const LIMIT: int = 3;
