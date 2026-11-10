// expect: reject src/lib/view.tsx: the "browser" field of src/lib/package.json is not supported
// Vite maps the relative imports of a package's modules through an object "browser" field of its
// package.json: "./label" of src/lib/view.tsx loads src/lib/other.js, not src/lib/label.ts,
// which TypeScript read.
export const unused = 0;
