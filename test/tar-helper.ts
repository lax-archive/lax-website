// A minimal deterministic ustar writer for bundle tests: enough to produce
// tars shaped like the archive's sealed bundles, and — via the knobs — the
// attacker-shaped ones the bounded extractor must refuse.

export interface TarEntry {
  name: string;
  bytes?: Buffer;
  /** ustar typeflag; "0" (regular file) unless the test corrupts it. */
  type?: string;
  /** Lie about the payload size (truncation and cap tests). */
  claimSize?: number;
  /** Fill the ustar prefix field (the extractor rejects any use of it). */
  prefix?: string;
  /** Break the header checksum after computing it. */
  corruptChecksum?: boolean;
  /** Overwrite the ustar magic. */
  magic?: string;
}

function octal(value: number, width: number): Buffer {
  const text = value.toString(8).padStart(width - 1, "0");
  return Buffer.from(`${text}\0`, "latin1");
}

function header(entry: TarEntry): Buffer {
  const block = Buffer.alloc(512);
  block.write(entry.name, 0, 100, "latin1");
  octal(0o644, 8).copy(block, 100); // mode
  octal(0, 8).copy(block, 108); // uid
  octal(0, 8).copy(block, 116); // gid
  octal(entry.claimSize ?? entry.bytes?.length ?? 0, 12).copy(block, 124);
  octal(0, 12).copy(block, 136); // mtime — sealed bundles are epoch-zero
  block.write(entry.type ?? "0", 156, 1, "latin1");
  block.write(entry.magic ?? "ustar", 257, 6, "latin1");
  block.write("00", 263, 2, "latin1");
  if (entry.prefix) block.write(entry.prefix, 345, 155, "latin1");
  // Checksum: the field itself read as spaces.
  block.fill(0x20, 148, 156);
  let sum = 0;
  for (const byte of block) sum += byte;
  block.write(`${sum.toString(8).padStart(6, "0")}\0 `, 148, 8, "latin1");
  if (entry.corruptChecksum) block[0] = block[0]! ^ 0xff;
  return block;
}

/** Serialize entries as a plain ustar stream with the standard terminator. */
export function makeTar(entries: TarEntry[]): Buffer {
  const parts: Buffer[] = [];
  for (const entry of entries) {
    parts.push(header(entry));
    const bytes = entry.bytes ?? Buffer.alloc(0);
    parts.push(bytes);
    const padding = (512 - (bytes.length % 512)) % 512;
    if (padding) parts.push(Buffer.alloc(padding));
  }
  parts.push(Buffer.alloc(1024));
  return Buffer.concat(parts);
}
