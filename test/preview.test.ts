import { describe, expect, it } from "vitest";
import { previewRequestPath } from "../src/preview.js";

describe("preview request paths", () => {
  it("decodes valid paths and supplies index documents", () => {
    expect(previewRequestPath("/")).toBe("index.html");
    expect(previewRequestPath("/lax-000017/")).toBe("lax-000017/index.html");
    expect(previewRequestPath("/a%20file.html?ignored=yes")).toBe("a file.html");
  });

  it("rejects malformed percent escapes without throwing", () => {
    expect(() => previewRequestPath("/%E0%A4%A")).not.toThrow();
    expect(previewRequestPath("/%E0%A4%A")).toBeUndefined();
    expect(previewRequestPath("/%ZZ")).toBeUndefined();
  });
});
