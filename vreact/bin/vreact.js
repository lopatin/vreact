#!/usr/bin/env node
// Launcher: runs the TypeScript sources with Node's built-in type stripping.
import { spawnSync } from "node:child_process";
import path from "node:path";
import { fileURLToPath } from "node:url";
const here = path.dirname(fileURLToPath(import.meta.url));
const cli = path.join(here, "..", "src", "cli.ts");
const r = spawnSync(process.execPath, ["--no-warnings", "--experimental-strip-types", cli, ...process.argv.slice(2)], { stdio: "inherit" });
process.exit(r.status ?? 1);
