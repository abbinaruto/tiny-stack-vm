// tiny-stack-vm: interpreter for make.fun's tiny stack ISA v1 (Node 22).
import { mkdirSync, readdirSync, readFileSync, statSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// [opcode, immediate bytes, values popped, values pushed] for every opcode, flat.
const S = [0,0,0,0, 1,1,0,1, 2,4,0,1, 3,0,1,0, 4,0,1,2, 5,0,2,2, 6,0,2,3, 7,0,3,3, 16,0,2,1, 17,0,2,1, 18,0,2,1, 19,0,2,1, 20,0,2,1, 21,0,2,1, 22,0,2,1, 23,0,1,1, 24,0,2,1, 25,0,2,1, 26,0,2,1, 27,0,1,1, 28,0,2,1, 29,0,2,1, 30,0,2,1, 32,0,2,1, 33,0,2,1, 34,0,2,1, 48,2,0,0, 49,2,1,0, 50,2,1,0, 51,2,0,0, 52,0,0,0, 64,0,1,1, 65,0,2,0, 80,0,1,0, 81,0,1,0, 82,0,0,1, 83,0,1,0];
const IMM = new Int8Array(256).fill(-1);
const NEED = new Int8Array(256).fill(-1); // pops * 4 + pushes
for (let i = 0; i < S.length; i += 4) { IMM[S[i]] = S[i + 1]; NEED[S[i]] = S[i + 2] * 4 + S[i + 3]; }
const DIG = new Uint8Array(11);

function run(p: Uint8Array, inp: Uint8Array): { out: Uint8Array; code: number } {
  const n = p.length, D = new Int32Array(256);
  let sp = 0;
  const C = new Int32Array(64);
  let csp = 0;
  const M = new Int32Array(256);
  const out = new Uint8Array(65536);
  let olen = 0, inPos = 0, pc = 0, steps = 0;
  const T = (code: number) => ({ out: out.subarray(0, olen), code });
  for (;;) {
    if (steps === 1000000) return T(10); // step limit
    if (pc < 0 || pc >= n) return T(9); // pc outside the program
    const op = p[pc], imm = IMM[op];
    if (imm < 0) return T(5); // unknown opcode
    if (pc + imm >= n) return T(9); // immediate cut off by the program's end
    steps++;
    const next = pc + 1 + imm, need = NEED[op], pops = need >> 2, pushes = need & 3;
    if (sp < pops) return T(2); // stack underflow
    if (sp - pops + pushes > 256) return T(3); // stack overflow
    pc = next;
    switch (op) {
      case 0x00: return T(0);
      case 0x01: D[sp++] = (p[next - 1] << 24) >> 24; break; // PUSH8, sign-extended
      case 0x02: D[sp++] = p[next - 4] | (p[next - 3] << 8) | (p[next - 2] << 16) | (p[next - 1] << 24); break;
      case 0x03: sp--; break;
      case 0x04: D[sp] = D[sp - 1]; sp++; break;
      case 0x05: { const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; break; }
      case 0x06: D[sp] = D[sp - 2]; sp++; break;
      case 0x07: { const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break; }
      case 0x17: D[sp - 1] = -D[sp - 1] | 0; break; // NEG wraps
      case 0x1b: D[sp - 1] = ~D[sp - 1]; break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = D[sp - 1], a = D[sp - 2];
        let r: number;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b); // exact low 32 bits
        else if (op === 0x13) {
          if (b === 0) return T(4);
          r = a === -2147483648 && b === -1 ? a : (a / b) | 0; // truncates toward zero
        } else if (op === 0x14) {
          if (b === 0) return T(4);
          r = b === -1 ? 0 : (a % b) | 0; // remainder takes the sign of a
        } else if (op === 0x15) {
          if (b === 0) return T(4);
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0; // unsigned
        } else if (op === 0x16) {
          if (b === 0) return T(4);
          r = ((a >>> 0) % (b >>> 0)) | 0; // unsigned
        } else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31);
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU, unsigned
        sp -= 2; D[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: {
        const rel = ((p[next - 2] | (p[next - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) { const v = D[--sp]; take = op === 0x31 ? v === 0 : v !== 0; }
        if (take) pc = next + rel;
        break;
      }
      case 0x33: // CALL: unsigned 16-bit absolute target
        if (csp === 64) return T(7);
        C[csp++] = next; pc = p[next - 2] | (p[next - 1] << 8);
        break;
      case 0x34:
        if (csp === 0) return T(8);
        pc = C[--csp];
        break;
      case 0x40: { // LOAD
        const addr = D[sp - 1];
        if (addr < 0 || addr >= 256) return T(6);
        D[sp - 1] = M[addr];
        break;
      }
      case 0x41: { // STORE: ( v addr -- )
        const addr = D[sp - 1], v = D[sp - 2];
        if (addr < 0 || addr >= 256) return T(6);
        sp -= 2; M[addr] = v;
        break;
      }
      case 0x50: { // PRINT: decimal ASCII, no newline; over the limit traps 11, writes nothing
        const v = D[sp - 1];
        let u = v < 0 ? -v : v, d = 0;
        do { DIG[d++] = 48 + (u % 10); u = Math.floor(u / 10); } while (u > 0);
        const len = d + (v < 0 ? 1 : 0);
        if (olen + len > 65536) return T(11);
        sp--;
        if (v < 0) out[olen++] = 45;
        while (d > 0) out[olen++] = DIG[--d];
        break;
      }
      case 0x51:
        if (olen + 1 > 65536) return T(11);
        out[olen++] = D[--sp] & 255;
        break;
      case 0x52:
        D[sp++] = inPos < inp.length ? inp[inPos++] : -1;
        break;
      case 0x53:
        return T(D[--sp] & 255);
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  // Skip anything that is not an instance directory (a stray file in /input
  // used to abort the whole run when program.bin was read from it).
  let isDir = false;
  try { isDir = statSync(join(I, id)).isDirectory(); } catch { isDir = false; }
  if (!isDir) continue;
  let inp: Uint8Array;
  try { inp = new Uint8Array(readFileSync(join(I, id, 'input.bin'))); } catch { inp = new Uint8Array(0); }
  let prog: Uint8Array;
  try { prog = new Uint8Array(readFileSync(join(I, id, 'program.bin'))); } catch { prog = new Uint8Array(0); }
  const r = run(prog, inp);
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), `${r.code}\n`);
}
