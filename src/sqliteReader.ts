/**
 * AM I GOOD AT VIBE — minimal pure-JS SQLite reader (no native dep, no CLI).
 *
 * Why this exists: the IDE chat-cache importer needs to read VS Code / Cursor
 * `state.vscdb` files (a `ItemTable(key TEXT, value BLOB)` SQLite database).
 * The previous implementation shelled out to the system `sqlite3` CLI, which
 * macOS / Linux ship but Windows does not — so the whole feature was a no-op on
 * Windows. This reader parses the on-disk SQLite file format directly in JS so
 * the importer works identically on every platform with zero dependencies.
 *
 * Scope is deliberately tiny: it reads complete rows of a single table by name.
 * It supports table b-trees (interior + leaf), overflow pages, and the standard
 * record/serial-type encoding — enough for `state.vscdb`. It is read-only and
 * never mutates the file. Anything it doesn't understand → it throws / returns
 * nothing, and the caller treats that as "no data".
 *
 * Reference: https://www.sqlite.org/fileformat2.html
 */

import * as fs from "fs";

const SQLITE_MAGIC = "SQLite format 3\0";

/** A decoded column value. Text/blob come back as strings; ints as numbers. */
export type SqliteValue = string | number | bigint | null;

/** Read a SQLite varint (big-endian, 1–9 bytes). Returns [value, byteLength]. */
function readVarint(buf: Buffer, offset: number): [bigint, number] {
  let result = 0n;
  for (let i = 0; i < 8; i++) {
    const byte = buf[offset + i];
    result = (result << 7n) | BigInt(byte & 0x7f);
    if ((byte & 0x80) === 0) return [result, i + 1];
  }
  // 9th byte contributes all 8 bits.
  result = (result << 8n) | BigInt(buf[offset + 8]);
  return [result, 9];
}

/** Convert a varint to a Number; safe for the lengths/counts we deal with. */
function num(v: bigint): number {
  return Number(v);
}

interface DbHeader {
  pageSize: number;
  /** Usable page size = pageSize - reserved bytes. */
  usable: number;
  /** Text encoding: 1 = UTF-8, 2 = UTF-16le, 3 = UTF-16be. */
  encoding: number;
}

function parseHeader(buf: Buffer): DbHeader {
  if (buf.length < 100 || buf.toString("latin1", 0, 16) !== SQLITE_MAGIC) {
    throw new Error("not a SQLite database");
  }
  let pageSize = buf.readUInt16BE(16);
  if (pageSize === 1) pageSize = 65536; // documented sentinel for 64 KiB pages
  const reserved = buf.readUInt8(20);
  const encoding = buf.readUInt32BE(56) || 1;
  return { pageSize, usable: pageSize - reserved, encoding };
}

/** Bytes of payload stored locally on a table-leaf cell before overflow. */
function localPayloadLen(P: number, usable: number): number {
  const maxLocal = usable - 35;
  if (P <= maxLocal) return P;
  const minLocal = Math.floor(((usable - 12) * 32) / 255) - 23;
  const K = minLocal + ((P - minLocal) % (usable - 4));
  return K <= maxLocal ? K : minLocal;
}

/** Reassemble a cell's full payload, following overflow pages if present. */
function readCellPayload(buf: Buffer, cellOffset: number, header: DbHeader): Buffer {
  const { pageSize, usable } = header;
  let p = cellOffset;
  const [payloadLenV, n1] = readVarint(buf, p);
  p += n1;
  // Skip the rowid varint (we don't need it).
  const [, n2] = readVarint(buf, p);
  p += n2;

  const P = num(payloadLenV);
  const local = localPayloadLen(P, usable);
  const parts: Buffer[] = [buf.subarray(p, p + local)];
  let remaining = P - local;

  if (remaining > 0) {
    let overflow = buf.readUInt32BE(p + local);
    const guard = new Set<number>();
    while (overflow !== 0 && remaining > 0 && !guard.has(overflow)) {
      guard.add(overflow);
      const base = (overflow - 1) * pageSize;
      const next = buf.readUInt32BE(base);
      const chunk = Math.min(usable - 4, remaining);
      parts.push(buf.subarray(base + 4, base + 4 + chunk));
      remaining -= chunk;
      overflow = next;
    }
  }
  return Buffer.concat(parts);
}

function decodeText(buf: Buffer, encoding: number): string {
  if (encoding === 2) return buf.toString("utf16le");
  if (encoding === 3) return buf.swap16().toString("utf16le"); // UTF-16be → swap → le
  return buf.toString("utf8");
}

/** Parse one record (the payload of a table cell) into its column values. */
function parseRecord(payload: Buffer, encoding: number): SqliteValue[] {
  const [headerLenV, n] = readVarint(payload, 0);
  const headerEnd = num(headerLenV);
  const serials: number[] = [];
  let h = n;
  while (h < headerEnd) {
    const [st, sn] = readVarint(payload, h);
    serials.push(num(st));
    h += sn;
  }

  const values: SqliteValue[] = [];
  let body = headerEnd;
  for (const st of serials) {
    if (st === 0) {
      values.push(null);
    } else if (st >= 1 && st <= 6) {
      // Sizes for serial types 1..6: 1, 2, 3, 4, 6, 8 bytes (big-endian signed).
      const size = [0, 1, 2, 3, 4, 6, 8][st];
      // readIntBE handles up to 6 bytes; 8-byte ints (st=6) use a BigInt read.
      values.push(size <= 6 ? payload.readIntBE(body, size) : payload.readBigInt64BE(body));
      body += size;
    } else if (st === 7) {
      values.push(payload.readDoubleBE(body));
      body += 8;
    } else if (st === 8) {
      values.push(0);
    } else if (st === 9) {
      values.push(1);
    } else if (st >= 12 && st % 2 === 0) {
      const len = (st - 12) / 2;
      values.push(decodeText(payload.subarray(body, body + len), 1)); // BLOB → utf8 text
      body += len;
    } else if (st >= 13) {
      const len = (st - 13) / 2;
      values.push(decodeText(payload.subarray(body, body + len), encoding));
      body += len;
    } else {
      values.push(null); // reserved serial types 10/11
    }
  }
  return values;
}

/** Recursively collect every leaf-cell payload of a table b-tree. */
function collectLeafPayloads(
  buf: Buffer,
  header: DbHeader,
  pageNum: number,
  out: Buffer[],
  visited: Set<number>
): void {
  if (visited.has(pageNum)) return; // cycle guard
  visited.add(pageNum);

  const pageBase = (pageNum - 1) * header.pageSize;
  // Page 1 carries the 100-byte file header before its b-tree header.
  const hdr = pageNum === 1 ? pageBase + 100 : pageBase;
  const type = buf.readUInt8(hdr);
  const numCells = buf.readUInt16BE(hdr + 3);
  const isInterior = type === 5 || type === 2;
  const cellPtrArray = hdr + (isInterior ? 12 : 8);

  if (type === 13) {
    // Table leaf.
    for (let i = 0; i < numCells; i++) {
      const cellPtr = buf.readUInt16BE(cellPtrArray + i * 2);
      out.push(readCellPayload(buf, pageBase + cellPtr, header));
    }
  } else if (type === 5) {
    // Table interior: each cell points to a left child; header has a right ptr.
    for (let i = 0; i < numCells; i++) {
      const cellPtr = buf.readUInt16BE(cellPtrArray + i * 2);
      const child = buf.readUInt32BE(pageBase + cellPtr);
      collectLeafPayloads(buf, header, child, out, visited);
    }
    const rightMost = buf.readUInt32BE(hdr + 8);
    collectLeafPayloads(buf, header, rightMost, out, visited);
  }
  // Index pages (2/10) are irrelevant for whole-table row reads.
}

/** Find a table's root page by scanning sqlite_master (rooted at page 1). */
function findTableRootPage(buf: Buffer, header: DbHeader, tableName: string): number | null {
  const payloads: Buffer[] = [];
  collectLeafPayloads(buf, header, 1, payloads, new Set());
  for (const payload of payloads) {
    // sqlite_master columns: type, name, tbl_name, rootpage, sql
    const cols = parseRecord(payload, header.encoding);
    if (cols[0] === "table" && cols[1] === tableName) {
      const root = cols[3];
      return typeof root === "number" ? root : Number(root);
    }
  }
  return null;
}

/**
 * Read every row of `tableName` from the SQLite database at `dbPath`.
 * Returns an array of column-value arrays. Throws on a malformed / non-SQLite
 * file or a missing table; callers should treat that as "no data".
 */
export function readTableRows(dbPath: string, tableName: string): SqliteValue[][] {
  const buf = fs.readFileSync(dbPath);
  const header = parseHeader(buf);
  const root = findTableRootPage(buf, header, tableName);
  if (root == null) throw new Error(`table not found: ${tableName}`);

  const payloads: Buffer[] = [];
  collectLeafPayloads(buf, header, root, payloads, new Set());
  return payloads.map((p) => parseRecord(p, header.encoding));
}
