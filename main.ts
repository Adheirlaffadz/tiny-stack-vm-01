import { mkdirSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Tiny stack VM: one run answers every instance in the input dir.
// Semantics follow ISA.md / vm.mjs exactly: wrap-around int32 arithmetic,
// traps in ISA order, step and output limits.
function exec(prog, inp) {
  const n = prog.length;
  const S = new Int32Array(256), R = new Int32Array(64), M = new Int32Array(256);
  const O = new Uint8Array(65536);
  let sp = 0, rp = 0, pc = 0, steps = 0, olen = 0, ip = 0;
  const finish = (c) => ({ b: O.slice(0, olen), c });
  for (;;) {
    if (steps === 1000000) return finish(10);
    if (pc < 0 || pc >= n) return finish(9);
    const op = prog[pc];
    let im = 0, po = 0, pu = 0;
    switch (op) {
      case 0: case 0x34: break;
      case 1: im = 1; pu = 1; break;
      case 2: im = 4; pu = 1; break;
      case 3: case 0x50: case 0x51: case 0x53: po = 1; break;
      case 0x31: case 0x32: im = 2; po = 1; break;
      case 4: po = 1; pu = 2; break;
      case 5: po = 2; pu = 2; break;
      case 6: po = 2; pu = 3; break;
      case 7: po = 3; pu = 3; break;
      case 0x17: case 0x1b: case 0x40: po = 1; pu = 1; break;
      case 0x30: case 0x33: im = 2; break;
      case 0x41: po = 2; break;
      case 0x52: pu = 1; break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: po = 2; pu = 1; break;
      default: return finish(5);
    }
    if (pc + im >= n) return finish(9);
    steps++;
    const nx = pc + 1 + im;
    if (sp < po) return finish(2);
    if (sp - po + pu > 256) return finish(3);
    pc = nx;
    if (op === 0) return finish(0);
    if (op === 1) { S[sp++] = (prog[nx - 1] << 24) >> 24; continue; }
    if (op === 2) { S[sp++] = prog[nx - 4] | (prog[nx - 3] << 8) | (prog[nx - 2] << 16) | (prog[nx - 1] << 24); continue; }
    if (op === 3) { sp--; continue; }
    if (op === 4) { S[sp] = S[sp - 1]; sp++; continue; }
    if (op === 5) { const t = S[sp - 1]; S[sp - 1] = S[sp - 2]; S[sp - 2] = t; continue; }
    if (op === 6) { S[sp] = S[sp - 2]; sp++; continue; }
    if (op === 7) { const a = S[sp - 3]; S[sp - 3] = S[sp - 2]; S[sp - 2] = S[sp - 1]; S[sp - 1] = a; continue; }
    if (op === 0x17) { S[sp - 1] = -S[sp - 1] | 0; continue; }
    if (op === 0x1b) { S[sp - 1] = ~S[sp - 1]; continue; }
    if (op >= 0x10 && op <= 0x22) {
      const b = S[sp - 1], a = S[sp - 2];
      let r = 0;
      if (op === 0x10) r = (a + b) | 0;
      else if (op === 0x11) r = (a - b) | 0;
      else if (op === 0x12) r = Math.imul(a, b);
      else if (op === 0x13) { if (b === 0) return finish(4); r = a === -2147483648 && b === -1 ? a : (a / b) | 0; }
      else if (op === 0x14) { if (b === 0) return finish(4); r = b === -1 ? 0 : (a % b) | 0; }
      else if (op === 0x15) { if (b === 0) return finish(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; }
      else if (op === 0x16) { if (b === 0) return finish(4); r = ((a >>> 0) % (b >>> 0)) | 0; }
      else if (op === 0x18) r = a & b;
      else if (op === 0x19) r = a | b;
      else if (op === 0x1a) r = a ^ b;
      else if (op === 0x1c) r = a << (b & 31);
      else if (op === 0x1d) r = a >> (b & 31);
      else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
      else if (op === 0x20) r = a === b ? 1 : 0;
      else if (op === 0x21) r = a < b ? 1 : 0;
      else if (op === 0x22) r = (a >>> 0) < (b >>> 0) ? 1 : 0;
      sp -= 2; S[sp++] = r; continue;
    }
    if (op === 0x30 || op === 0x31 || op === 0x32) {
      const rel = ((prog[nx - 2] | (prog[nx - 1] << 8)) << 16) >> 16;
      let go = true;
      if (op !== 0x30) { const v = S[--sp]; go = op === 0x31 ? v === 0 : v !== 0; }
      if (go) pc = nx + rel;
      continue;
    }
    if (op === 0x33) { if (rp === 64) return finish(7); R[rp++] = nx; pc = prog[nx - 2] | (prog[nx - 1] << 8); continue; }
    if (op === 0x34) { if (rp === 0) return finish(8); pc = R[--rp]; continue; }
    if (op === 0x40) { const ad = S[sp - 1]; if (ad < 0 || ad >= 256) return finish(6); S[sp - 1] = M[ad]; continue; }
    if (op === 0x41) { const ad = S[sp - 1], v = S[sp - 2]; if (ad < 0 || ad >= 256) return finish(6); sp -= 2; M[ad] = v; continue; }
    if (op === 0x50) { const s = String(S[sp - 1]); if (olen + s.length > 65536) return finish(11); sp--; for (let i = 0; i < s.length; i++) O[olen++] = s.charCodeAt(i); continue; }
    if (op === 0x51) { if (olen + 1 > 65536) return finish(11); O[olen++] = S[--sp] & 255; continue; }
    if (op === 0x52) { S[sp++] = ip < inp.length ? inp[ip++] : -1; continue; }
    if (op === 0x53) return finish(S[--sp] & 255);
  }
}

const IN = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(IN).sort()) {
  try {
    const r = exec(readFileSync(join(IN, id, 'program.bin')), readFileSync(join(IN, id, 'input.bin')));
    mkdirSync(join(OUT, id), { recursive: true });
    writeFileSync(join(OUT, id, 'stdout.bin'), r.b);
    writeFileSync(join(OUT, id, 'exit.txt'), r.c + '\n');
  } catch {
    mkdirSync(join(OUT, id), { recursive: true });
    writeFileSync(join(OUT, id, 'stdout.bin'), '');
    writeFileSync(join(OUT, id, 'exit.txt'), '1\n');
  }
}
