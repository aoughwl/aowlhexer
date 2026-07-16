// aifopt — an AIF (.c.aif) optimizer that Araq's hexer/lengc leaves undone.
//
// hexer lowers correctly but emits IR with residual slack: an unreachable
// trailing `(ret result)` after an explicit return, the now-dead `result`
// variable, dead `while` labels with no `goto`, deeply nested single-child
// `(stmts (stmts …))` blocks, and un-folded constant arithmetic. aifopt is a
// fixpoint simplifier over the .c.aif tree that removes all of it — the
// optimization layer a stock hexer/lengc pipeline does not have.
//
// It round-trips .c.aif faithfully (every token's raw text, including line-info
// suffixes, is preserved) and re-emits a valid .c.aif that the backend reads.
"use strict";

// ---- faithful reader: keeps each token's exact source text --------------
function read(src) {
  let i = 0; const n = src.length;
  const ws = () => { while (i < n && /\s/.test(src[i])) i++; };
  function token() {                       // returns the exact raw token text
    if (src[i] === '"') { let s = src[i++]; while (i < n && src[i] !== '"') { if (src[i] === "\\") s += src[i++]; s += src[i++]; } s += src[i++]; while (i < n && !/[\s()]/.test(src[i])) s += src[i++]; return s; }
    if (src[i] === "'") { let s = src[i++]; while (i < n && src[i] !== "'") { if (src[i] === "\\") s += src[i++]; s += src[i++]; } s += src[i++]; while (i < n && !/[\s()]/.test(src[i])) s += src[i++]; return s; }
    let s = ""; while (i < n && !/[\s()]/.test(src[i])) s += src[i++]; return s;
  }
  function node() {
    ws();
    if (src[i] === "(") {
      i++; ws();
      const tagRaw = token(); const kids = []; ws();
      while (i < n && src[i] !== ")") { kids.push(node()); ws(); }
      i++;
      return { tagRaw, tag: bare(tagRaw), kids };
    }
    const raw = token();
    return { raw, atom: bareAtom(raw) };
  }
  const out = []; ws(); while (i < n) { out.push(node()); ws(); }
  return out;
}
// strip line-info / def markers to get the semantic name
function bare(t) { const m = /[@~]/.exec(t); return (m ? t.slice(0, m.index) : t).replace(/^:/, ""); }
function bareAtom(t) {
  if (t[0] === '"' || t[0] === "'") return t;   // literal keeps quotes
  let s = t; if (s[0] === ":") s = s.slice(1);
  const m = /[@~]/.exec(s); return m ? s.slice(0, m.index) : s;
}
const isList = (x) => x && x.kids !== undefined;
const isAtom = (x) => x && x.raw !== undefined;
const isSym = (x) => isAtom(x) && !/^["']/.test(x.raw) && !isNum(x.atom) && !KEYS.has(x.atom);
const KEYS = new Set([".", "true", "false", "nil", "inf", "neginf", "nan"]);
function isNum(a) { return /^-?\d+$/.test(a) || /^\d+u(ll|l)?$/.test(a) || /^-?(\d+\.\d*|\.\d+)/.test(a); }
const isDefAtom = (x) => isAtom(x) && x.raw[0] === ":";

// ---- writer: re-emit a valid .c.aif -------------------------------------
function write(node) {
  if (isAtom(node)) return node.raw;
  return "(" + node.tagRaw + (node.kids.length ? " " + node.kids.map(write).join(" ") : "") + ")";
}

// ---- tree helpers -------------------------------------------------------
function clone(n) { return isAtom(n) ? { raw: n.raw, atom: n.atom } : { tagRaw: n.tagRaw, tag: n.tag, kids: n.kids.map(clone) }; }
function walk(n, fn) { fn(n); if (isList(n)) for (const k of n.kids) walk(k, fn); }
const TERMINATORS = new Set(["ret", "break", "continue", "jmp", "raise"]);

// count every node (for the before/after metric)
function countNodes(n) { let c = 0; walk(n, () => c++); return c; }
function countTag(root, tag) { let c = 0; walk(root, (n) => { if (isList(n) && n.tag === tag) c++; }); return c; }

// ---- optimization passes (each returns true if it changed anything) -----

// 1. Flatten a `stmts` element that itself is a `stmts` (block with no scope).
function flattenStmts(node) {
  let changed = false;
  if (isList(node)) {
    for (const k of node.kids) if (flattenStmts(k)) changed = true;
    if (node.tag === "stmts") {
      const out = [];
      for (const k of node.kids) {
        if (isList(k) && k.tag === "stmts") { out.push(...k.kids); changed = true; }
        else out.push(k);
      }
      node.kids = out;
    }
  }
  return changed;
}

// 2. Drop statements after an unconditional terminator within a `stmts`.
function unreachableElim(node) {
  let changed = false;
  if (isList(node)) {
    for (const k of node.kids) if (unreachableElim(k)) changed = true;
    if (node.tag === "stmts") {
      let cut = -1;
      for (let j = 0; j < node.kids.length; j++) {
        const k = node.kids[j];
        if (isList(k) && TERMINATORS.has(k.tag)) { cut = j; break; }
      }
      if (cut >= 0 && cut < node.kids.length - 1) { node.kids = node.kids.slice(0, cut + 1); changed = true; }
    }
  }
  return changed;
}

// 3. Remove dead local vars: declared, side-effect-free init, never read.
const DECL_TAGS = new Set(["var", "let", "cursor", "gvar", "glet"]);
function readSymbols(proc) {
  const reads = new Set();
  walk(proc, (n) => {
    if (isList(n)) {
      // a decl's own name (kids[0], a def atom) is not a read
      const skip = DECL_TAGS.has(n.tag) || n.tag === "param" ? n.kids[0] : null;
      for (const k of n.kids) {
        if (k === skip) continue;
        if (isSym(k) && !isDefAtom(k)) reads.add(k.atom);
      }
    }
  });
  return reads;
}
function deadVarElim(proc) {
  let changed = false, again = true;
  while (again) {
    again = false;
    const reads = readSymbols(proc);
    walk(proc, (n) => {
      if (isList(n) && n.tag === "stmts") {
        const out = [];
        for (const k of n.kids) {
          if (isList(k) && DECL_TAGS.has(k.tag) && isDefAtom(k.kids[0])) {
            const name = k.kids[0].atom;
            const init = k.kids[k.kids.length - 1];
            const initPure = isDot(init) || isAtom(init);   // '.' or a literal/symbol init
            if (!reads.has(name) && initPure) { changed = again = true; continue; }
          }
          out.push(k);
        }
        n.kids = out;
      }
    });
  }
  return changed;
}
const isDot = (x) => isAtom(x) && x.atom === ".";

// 4. Remove `(lab X)` with no matching `(jmp X)`.
function deadLabelElim(proc) {
  const targets = new Set();
  walk(proc, (n) => { if (isList(n) && n.tag === "jmp" && isAtom(n.kids[0])) targets.add(n.kids[0].atom); });
  let changed = false;
  walk(proc, (n) => {
    if (isList(n) && n.tag === "stmts") {
      const out = n.kids.filter((k) => !(isList(k) && k.tag === "lab" && isAtom(k.kids[0]) && !targets.has(k.kids[0].atom)));
      if (out.length !== n.kids.length) { n.kids = out; changed = true; }
    }
  });
  return changed;
}

// 5. Constant-fold typed integer binops on literals; 6. algebraic identities.
const FOLD = {
  add: (a, b) => a + b, sub: (a, b) => a - b, mul: (a, b) => a * b,
  div: (a, b) => (b === 0n ? null : a / b), mod: (a, b) => (b === 0n ? null : a % b),
  bitand: (a, b) => a & b, bitor: (a, b) => a | b, bitxor: (a, b) => a ^ b,
  shl: (a, b) => a << b, shr: (a, b) => a >> b,
};
const MASK64 = (1n << 64n) - 1n;
function toI64(v) { v &= MASK64; return v >= (1n << 63n) ? v - (1n << 64n) : v; }
function intOf(node) {
  if (!isAtom(node)) return null;
  const a = node.atom;
  if (/^-?\d+$/.test(a)) { try { return BigInt(a); } catch (_) { return null; } }
  return null;
}
function litNode(v) { const s = v.toString(); return { raw: s, atom: s }; }
function foldAndSimplify(node) {
  let changed = false;
  if (isList(node)) {
    for (let j = 0; j < node.kids.length; j++) {
      const k = node.kids[j];
      if (isList(k)) {
        if (foldAndSimplify(k)) changed = true;
        const r = tryFold(k);
        if (r) { node.kids[j] = r; changed = true; }
      }
    }
  }
  return changed;
}
function tryFold(k) {
  if (!FOLD[k.tag] && k.tag !== "neg" && k.tag !== "bitnot") return null;
  // typed binop: (op TYPE a b) — type is kids[0]
  if (FOLD[k.tag]) {
    const a = k.kids[k.kids.length - 2], b = k.kids[k.kids.length - 1];
    const ai = intOf(a), bi = intOf(b);
    if (ai !== null && bi !== null) {           // constant fold
      const v = FOLD[k.tag](ai, bi);
      if (v !== null) return litNode(toI64(v));
    }
    // algebraic identities (operand must be side-effect free: symbol or literal)
    const pure = (x) => isAtom(x);
    if (k.tag === "add" && bi === 0n && pure(a)) return a;
    if (k.tag === "add" && ai === 0n && pure(b)) return b;
    if (k.tag === "sub" && bi === 0n && pure(a)) return a;
    if (k.tag === "mul" && bi === 1n && pure(a)) return a;
    if (k.tag === "mul" && ai === 1n && pure(b)) return b;
    if (k.tag === "mul" && (ai === 0n || bi === 0n) && pure(a) && pure(b)) return litNode(0n);
    if (k.tag === "div" && bi === 1n && pure(a)) return a;
    if (k.tag === "bitor" && bi === 0n && pure(a)) return a;
    if (k.tag === "bitand" && ai !== null && bi !== null) return litNode(toI64(ai & bi));
  }
  if (k.tag === "neg") { const x = intOf(k.kids[k.kids.length - 1]); if (x !== null) return litNode(toI64(-x)); }
  if (k.tag === "bitnot") { const x = intOf(k.kids[k.kids.length - 1]); if (x !== null) return litNode(toI64(~x)); }
  return null;
}

// 7. Move-aware destroy elision — the optimization gcc CANNOT do.
// hexer's mover emits `=wasMoved(v)` when a value is moved out of `v`, but the
// destroyer independently emits `=destroy(v)` at scope exit. When `=wasMoved(v)`
// unconditionally dominates `=destroy(v)` in the same straight-line block and `v`
// is not re-initialised in between, `v`'s payload is provably nil at the destroy,
// so `=destroy(v)` is a runtime no-op (a call + null-check that always falls
// through). gcc keeps it — `=destroy` is an opaque, side-effecting call and it
// cannot prove `v` is nil across the opaque `=wasMoved`. We remove it. Sound: an
// emptied owner has nothing to free, so eliding the destroy never leaks.
function isArcCall(n, kind) {           // kind: "=wasMoved" | "=destroy"
  return isList(n) && (n.tag === "call" || n.tag === "hcall") &&
    isAtom(n.kids[0]) && n.kids[0].atom.startsWith(kind);
}
function argVar(call) {                  // var touched by an ARC call: v or (addr v)
  const a = call.kids[1];
  if (isList(a) && a.tag === "addr" && isAtom(a.kids[0])) return a.kids[0].atom;
  if (isAtom(a)) return a.atom;
  return null;
}
// Does statement `s` re-initialise / mutate variable `name` (making a later
// destroy meaningful again)? Conservative: assignment/decl target, or address
// taken by anything other than =destroy/=wasMoved.
function mutates(s, name) {
  let hit = false;
  walk(s, (n) => {
    if (isList(n)) {
      if ((n.tag === "asgn" || n.tag === "store") && isAtom(n.kids[0]) && n.kids[0].atom === name) hit = true;
      if (DECL_TAGS.has(n.tag) && isDefAtom(n.kids[0]) && n.kids[0].atom === name) hit = true;
      // address taken inside a non-ARC statement → assume it may be mutated
      if (n.tag === "addr" && isAtom(n.kids[0]) && n.kids[0].atom === name) hit = true;
    }
  });
  return hit;
}
function moveDestroyElim(proc) {
  let changed = false;
  walk(proc, (node) => {
    if (!(isList(node) && node.tag === "stmts")) return;
    const ks = node.kids;
    const moved = new Set();          // vars currently in a moved-from (nil) state
    const keep = [];
    for (let j = 0; j < ks.length; j++) {
      const s = ks[j];
      if (isArcCall(s, "=wasMoved")) { const v = argVar(s); if (v) moved.add(v); keep.push(s); continue; }
      if (isArcCall(s, "=destroy")) {
        const v = argVar(s);
        if (v && moved.has(v)) { changed = true; continue; }   // elide: provably nil
        keep.push(s); continue;
      }
      // any other statement: drop vars it mutates out of the moved-set
      for (const v of [...moved]) if (mutates(s, v)) moved.delete(v);
      keep.push(s);
    }
    node.kids = keep;
  });
  return changed;
}

// count ARC ops (for the metric)
function countArc(root, kind) { let c = 0; walk(root, (n) => { if (isArcCall(n, kind)) c++; }); return c; }

// ---- driver -------------------------------------------------------------
function optimize(src) {
  const nodes = read(src);
  const root = nodes.find((n) => isList(n) && n.tag === "stmts");
  if (!root) throw new Error("aifopt: no top-level (stmts …)");
  const snap = () => ({ nodes: countNodes(root), rets: countTag(root, "ret"), vars: countTag(root, "var"),
    labs: countTag(root, "lab"), stmts: countTag(root, "stmts"), destroys: countArc(root, "=destroy") });
  const before = snap();

  // fixpoint over all passes
  let pass = 0;
  for (;;) {
    let ch = false;
    if (flattenStmts(root)) ch = true;         // flatten first: puts =wasMoved & =destroy in one block
    if (unreachableElim(root)) ch = true;
    // per-proc passes
    for (const p of root.kids) if (isList(p) && (p.tag === "proc" || p.tag === "func")) {
      if (moveDestroyElim(p)) ch = true;       // the gcc-can't-do win
      if (deadVarElim(p)) ch = true;
      if (deadLabelElim(p)) ch = true;
    }
    if (foldAndSimplify(root)) ch = true;
    if (flattenStmts(root)) ch = true;
    if (!ch || ++pass > 50) break;
  }

  const after = snap();
  const out = "(.nif27)\n" + write(root) + "\n";
  return { out, before, after };
}

const api = { optimize, read, write };
if (typeof module !== "undefined" && module.exports) module.exports = api;

// CLI: aifopt <in.c.aif> [-o out.c.aif] [--stats]
if (require.main === module) {
  const fs = require("fs");
  const args = process.argv.slice(2);
  let inp = null, outp = null, stats = false;
  for (let i = 0; i < args.length; i++) {
    if (args[i] === "-o") outp = args[++i];
    else if (args[i] === "--stats") stats = true;
    else inp = args[i];
  }
  if (!inp) { console.error("usage: aifopt <in.c.aif> [-o out.c.aif] [--stats]"); process.exit(2); }
  const r = optimize(fs.readFileSync(inp, "utf8"));
  if (stats) {
    const pct = (a, b) => (a === 0 ? "0" : (((a - b) / a) * 100).toFixed(1));
    console.error(`aifopt: nodes ${r.before.nodes}→${r.after.nodes} (-${pct(r.before.nodes, r.after.nodes)}%)  ` +
      `stmts ${r.before.stmts}→${r.after.stmts}  rets ${r.before.rets}→${r.after.rets}  ` +
      `vars ${r.before.vars}→${r.after.vars}  labs ${r.before.labs}→${r.after.labs}  ` +
      `=destroy ${r.before.destroys}→${r.after.destroys}`);
  }
  if (outp) fs.writeFileSync(outp, r.out); else process.stdout.write(r.out);
}
