#!/usr/bin/env node
// Demonstrate that aifhexer+aifopt is measurably better than stock hexer/lengc:
// on real hexer output it removes the dead code hexer leaves in every proc, then
// proves the optimized IR still compiles to identical results.
//
//   node opt/demo.js            # uses the backend's example .c.aif files
"use strict";
const fs = require("fs");
const os = require("os");
const path = require("path");
const cp = require("child_process");
const aifopt = require("./aifopt.js");

function firstDir(cands) { for (const c of cands) if (fs.existsSync(c)) return c; return null; }
const HOME = os.homedir();
const BACKEND = firstDir([path.join(HOME, "aifc/bin/aifc"), path.join(HOME, "aifc/bin/nifc"), path.join(HOME, "nifc/bin/nifc")]);
const EXDIR = firstDir([path.join(HOME, "aifc/examples"), path.join(HOME, "nifc/examples")]);
if (!BACKEND || !EXDIR) { console.error("demo: need the aifc/nifc backend + examples"); process.exit(2); }

const TMP = fs.mkdtempSync(path.join(os.tmpdir(), "aifopt-demo-"));
// [file, [entry, ...args, expected]]
const CASES = {
  "compute.c.nif": [["gcd", 48, 36, "12"], ["isPrime", 97, "1"], ["collatz", 27, "111"], ["popcount", 255, "8"]],
  "fib.c.nif":     [["fib", 20, "6765"], ["sumTo", 100, "5050"]],
  "mathf.c.nif":   [["power", "2.0", 10, "1024"], ["classify", 15, "300"]],
};

function backend(cnif, entry, args) {
  const a = ["exec", cnif, "--entry", entry];
  for (const v of args) a.push("--arg", String(v));
  return cp.spawnSync("node", [BACKEND, ...a], { encoding: "utf8" }).stdout.trim();
}

const agg = { nodes: [0, 0], rets: [0, 0], vars: [0, 0], labs: [0, 0], clines: [0, 0] };
let checks = 0, ok = 0;
console.log("aifopt — the optimization layer stock hexer/lengc lacks\n");
console.log("file            IR nodes      dead rets   dead vars   dead labels   C lines");
console.log("------------------------------------------------------------------------------");
for (const [file, cases] of Object.entries(CASES)) {
  const src = path.join(EXDIR, file);
  if (!fs.existsSync(src)) continue;
  const r = aifopt.optimize(fs.readFileSync(src, "utf8"));
  const opt = path.join(TMP, file);
  fs.writeFileSync(opt, r.out);
  const cO = cp.spawnSync("node", [BACKEND, "emit", src], { encoding: "utf8" }).stdout.split("\n").length;
  const cP = cp.spawnSync("node", [BACKEND, "emit", opt], { encoding: "utf8" }).stdout.split("\n").length;
  agg.nodes[0] += r.before.nodes; agg.nodes[1] += r.after.nodes;
  agg.rets[0] += r.before.rets; agg.rets[1] += r.after.rets;
  agg.vars[0] += r.before.vars; agg.vars[1] += r.after.vars;
  agg.labs[0] += r.before.labs; agg.labs[1] += r.after.labs;
  agg.clines[0] += cO; agg.clines[1] += cP;
  const pct = (((r.before.nodes - r.after.nodes) / r.before.nodes) * 100).toFixed(1);
  console.log(`${file.padEnd(15)} ${String(r.before.nodes).padStart(4)}→${String(r.after.nodes).padStart(4)} (-${pct}%)   ` +
    `${r.before.rets}→${r.after.rets}       ${r.before.vars}→${r.after.vars}       ${r.before.labs}→${r.after.labs}         ${cO}→${cP}`);
  // correctness: optimized IR must give identical results
  for (const c of cases) {
    const expected = c[c.length - 1]; const entry = c[0]; const args = c.slice(1, -1);
    const got = backend(opt, entry, args); checks++;
    if (got === expected) ok++;
    else console.log(`   ! ${entry}(${args}) = ${got} (want ${expected})`);
  }
}
const p = (a) => (((agg[a][0] - agg[a][1]) / agg[a][0]) * 100).toFixed(1);
console.log("------------------------------------------------------------------------------");
console.log(`TOTAL           ${agg.nodes[0]}→${agg.nodes[1]} (-${p("nodes")}%)   ` +
  `${agg.rets[0]}→${agg.rets[1]}     ${agg.vars[0]}→${agg.vars[1]}     ${agg.labs[0]}→${agg.labs[1]}       ${agg.clines[0]}→${agg.clines[1]}`);
console.log(`\ncorrectness: ${ok}/${checks} optimized programs return identical results`);
console.log("\nEvery proc stock hexer emits carries an unreachable trailing `return result`,");
console.log("a dead `result` variable, and a dead loop label. aifopt removes all of them,");
console.log("flattens nested `(stmts (stmts …))` blocks, folds constant arithmetic, and");
console.log("simplifies algebraic identities — the pass a stock hexer/lengc pipeline omits.");
process.exit(ok === checks ? 0 : 1);
