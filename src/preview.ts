/** Convert a preview-server request URL into a site-relative file path.
 * Invalid percent escapes are a bad request, not a reason to terminate the
 * long-running preview process. Filesystem containment is checked by the
 * caller after resolving this value below the output directory. */
export function previewRequestPath(requestUrl: string | undefined): string | undefined {
  try {
    const url = new URL(requestUrl ?? "/", "http://localhost");
    let relative = decodeURIComponent(url.pathname).replace(/^\/+/, "");
    if (relative === "" || relative.endsWith("/")) relative += "index.html";
    return relative;
  } catch {
    return undefined;
  }
}
