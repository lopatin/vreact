// expect: reject is outside the project directory
// "src" outside the project (tests/.work/FaProjectSrcOutside/../../cases/FaProjectSrcOutside/shared):
// the tsconfig.json next to those sources (jsxImportSource preact) is the one Vite compiles them
// with, and VTS checked them with the project's (React). This file is not used.
export const unused = 0;
