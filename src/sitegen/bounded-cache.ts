/** LRU bounded by accounted bytes. Oversized entries remain usable by the
 * current caller but are never retained for later pages. */
export class BoundedCache<T> {
  private entries = new Map<string, { value: T; bytes: number }>();
  private bytes = 0;

  constructor(readonly limit: number) {
    if (!Number.isSafeInteger(limit) || limit < 0)
      throw new Error("memory cache budget must be a nonnegative safe integer");
  }

  get(key: string): T | undefined {
    const entry = this.entries.get(key);
    if (!entry) return undefined;
    this.entries.delete(key);
    this.entries.set(key, entry);
    return entry.value;
  }

  set(key: string, value: T, serializedBytes: number): void {
    const previous = this.entries.get(key);
    if (previous) { this.bytes -= previous.bytes; this.entries.delete(key); }
    // Account for object/string overhead as well as serialized content. This
    // is a conservative budget estimate, not a V8 heap-size measurement.
    const bytes = serializedBytes * 4 + key.length * 2 + 256;
    if (bytes > this.limit) return;
    while (this.bytes + bytes > this.limit) {
      const oldest = this.entries.keys().next().value!;
      this.bytes -= this.entries.get(oldest)!.bytes;
      this.entries.delete(oldest);
    }
    this.entries.set(key, { value, bytes });
    this.bytes += bytes;
  }

  clear(): void { this.entries.clear(); this.bytes = 0; }
}
