// expect: reject src/lib/isnull/Counter.tsx: the "browser" field of src/lib/package.json is not supported ;; src/lib/bom/Counter.tsx: the "browser" field of src/lib/package.json is not supported ;; src/lib/sfx/Counter.tsx: the "browser" field of src/lib/package.json is not supported
// Vite maps a module's imports through the "browser" field of the nearest package.json it can
// load, and skips one whose loading throws: `null`, a byte order mark before the JSON, a
// "sideEffects" list with a non-string entry. Each nested package.json here is skipped, so
// "./limits" of src/lib/*/Counter.tsx loads src/lib/evil.js (LIMIT = 100), not the limits.ts
// TypeScript read (LIMIT = 3), and the invariant breaks on the 4th click.
export const unused = 0;
