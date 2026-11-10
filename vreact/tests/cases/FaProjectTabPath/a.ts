// expect: reject contains a tab, which is not supported: the bundler's dev server (vite) serves a module at the URL of its path, and the browser's URL parser drops tabs and line breaks in it
// Vite's dev server rewrites "./limits" of src/w<tab>v/Counter.tsx to the URL
// /src/w<tab>v/limits.ts; the browser's URL parser drops the tab and asks for /src/wv/limits.ts:
// src/wv/limits.ts runs (LIMIT = 100, excluded from the verified program), not
// src/w<tab>v/limits.ts, which TypeScript read (LIMIT = 3).
export const unused = 0;
