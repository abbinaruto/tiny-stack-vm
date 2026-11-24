// Tiny stack ISA v1 interpreter: one run answers every /input/<id>/ program.
import { readdirSync, readFileSync, mkdirSync, writeFileSync } from "node:fs";

// Per ISA.md: [byte, immediate bytes, pops, pushes].
const SPEC: [number, number, number, number][] = [
  [0x00,0,0,0],[0x01,1,0,1],[0x02,4,0,1],[0x03,0,1,0],
  [0x04,0,1,2],[0x05,0,2,2],[0x06,0,2,3],[0x07,0,3,3],
  [0x10,0,2,1],[0x11,0,2,1],[0x12,0,2,1],[0x13,0,2,1],
  [0x14,0,2,1],[0x15,0,2,1],[0x16,0,2,1],[0x17,0,1,1],
  [0x18,0,2,1],[0x19,0,2,1],[0x1a,0,2,1],[0x1b,0,1,1],
  [0x1c,0,2,1],[0x1d,0,2,1],[0x1e,0,2,1],[0x20,0,2,1],
  [0x21,0,2,1],[0x22,0,2,1],[0x30,2,0,0],[0x31,2,1,0],
  [0x32,2,1,0],[0x33,2,0,0],[0x34,0,0,0],[0x40,0,1,1],
  [0x41,0,2,0],[0x50,0,1,0],[0x51,0,1,0],[0x52,0,0,1],
  [0x53,0,1,0],
];
const IMM = new Uint8Array(256);
const NEED = new Uint8Array(256);
const GIVE = new Uint8Array(256);
const KNOWN = new Uint8Array(256);
for (const [op, imm, pops, pushes] of SPEC) {
  IMM[op] = imm;
  NEED[op] = pops;
  GIVE[op] = pushes;
  KNOWN[op] = 1;
}

type Result = { out: Uint8Array; exit: number };

function runVM(prog: Uint8Array, input: Uint8Array): Result {
  const n = prog.length;
  const stack = new Int32Array(256);
  let sp = 0;
  const calls = new Int32Array(64);
  let cp = 0;
  const mem = new Int32Array(256);
  const out = new Uint8Array(65536);
  let olen = 0;
  let ipos = 0;
  let pc = 0;
  let steps = 0;
  const finish = (exit: number): Result => ({ out: out.slice(0, olen), exit });

  for (;;) {
    if (steps >= 1000000) return finish(10);
    if (pc < 0 || pc >= n) return finish(9);
    const op = prog[pc];
    if (!KNOWN[op]) return finish(5);
    const imm = IMM[op];
    if (pc + imm >= n) return finish(9);
    steps++;
    if (sp < NEED[op]) return finish(2);
    if (sp - NEED[op] + GIVE[op] > 256) return finish(3);
    const base = pc;
    pc = base + 1 + imm;
    switch (op) {
      case 0x00:
        return finish(0);
      case 0x01:
        stack[sp++] = (prog[base + 1] << 24) >> 24;
        break;
      case 0x02:
        stack[sp++] = prog[base + 1] | (prog[base + 2] << 8) | (prog[base + 3] << 16) | (prog[base + 4] << 24);
        break;
      case 0x03:
        sp--;
        break;
      case 0x04:
        stack[sp] = stack[sp - 1];
        sp++;
        break;
      case 0x05: {
        const t = stack[sp - 1];
        stack[sp - 1] = stack[sp - 2];
        stack[sp - 2] = t;
        break;
      }
      case 0x06:
        stack[sp] = stack[sp - 2];
        sp++;
        break;
      case 0x07: {
        const t = stack[sp - 3];
        stack[sp - 3] = stack[sp - 2];
        stack[sp - 2] = stack[sp - 1];
        stack[sp - 1] = t;
        break;
      }
      case 0x17:
        stack[sp - 1] = (-stack[sp - 1]) | 0;
        break;
      case 0x1b:
        stack[sp - 1] = ~stack[sp - 1];
        break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = stack[sp - 1];
        const a = stack[sp - 2];
        let r = 0;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b);
        else if (op === 0x13) {
          if (b === 0) return finish(4);
          r = a === -2147483648 && b === -1 ? a : Math.trunc(a / b);
        } else if (op === 0x14) {
          if (b === 0) return finish(4);
          r = b === -1 ? 0 : a % b;
        } else if (op === 0x15) {
          if (b === 0) return finish(4);
          r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
        } else if (op === 0x16) {
          if (b === 0) return finish(4);
          r = ((a >>> 0) % (b >>> 0)) | 0;
        } else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31);
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        stack[sp - 2] = r;
        sp--;
        break;
      }
      case 0x30: case 0x31: case 0x32: {
        const rel = ((prog[base + 1] | (prog[base + 2] << 8)) << 16) >> 16;
        let go = op === 0x30;
        if (!go) {
          const v = stack[--sp];
          go = op === 0x31 ? v === 0 : v !== 0;
        }
        if (go) pc += rel;
        break;
      }
      case 0x33:
        if (cp === 64) return finish(7);
        calls[cp++] = pc;
        pc = prog[base + 1] | (prog[base + 2] << 8);
        break;
      case 0x34:
        if (cp === 0) return finish(8);
        pc = calls[--cp];
        break;
      case 0x40: {
        const addr = stack[sp - 1];
        if (addr < 0 || addr > 255) return finish(6);
        stack[sp - 1] = mem[addr];
        break;
      }
      case 0x41: {
        const addr = stack[sp - 1];
        const v = stack[sp - 2];
        if (addr < 0 || addr > 255) return finish(6);
        mem[addr] = v;
        sp -= 2;
        break;
      }
      case 0x50: {
        const text = String(stack[sp - 1]);
        if (olen + text.length > 65536) return finish(11);
        for (let i = 0; i < text.length; i++) out[olen++] = text.charCodeAt(i);
        sp--;
        break;
      }
      case 0x51:
        if (olen + 1 > 65536) return finish(11);
        out[olen++] = stack[--sp] & 255;
        break;
      case 0x52:
        stack[sp++] = ipos < input.length ? input[ipos++] : -1;
        break;
      case 0x53:
        return finish(stack[--sp] & 255);
    }
  }
}

// Driver: one run answers every instance directory under /input.
function readOrEmpty(path: string): Buffer {
  try {
    return readFileSync(path);
  } catch {
    return Buffer.alloc(0);
  }
}

let ids: string[] = [];
try {
  ids = readdirSync("/input", { withFileTypes: true })
    .filter((e) => e.isDirectory())
    .map((e) => e.name)
    .sort();
} catch {
  ids = [];
}

for (const id of ids) {
  const prog = readOrEmpty(`/input/${id}/program.bin`);
  const inp = readOrEmpty(`/input/${id}/input.bin`);
  const { out, exit } = runVM(prog, inp);
  mkdirSync(`/output/${id}`, { recursive: true });
  writeFileSync(`/output/${id}/stdout.bin`, out);
  writeFileSync(`/output/${id}/exit.txt`, String(exit));
}
