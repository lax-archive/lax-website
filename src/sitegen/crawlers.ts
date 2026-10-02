// What the site tells crawlers: robots.txt and the sitemap. Both are
// generated from the same file table the pages come from, so the sitemap
// can never name a page the build did not write.

import path from "node:path";
import { DEFAULT_SITE_URL } from "../config.js";
import { esc } from "./html.js";

const SITE_ROOT = `${DEFAULT_SITE_URL.replace(/\/+$/, "")}/`;

/**
 * Crawl everything but the branch previews: `/previews/` holds a copy of
 * the site per retained branch, published by the deploy workflow beside
 * production, and a crawler that indexes those sees every page in
 * duplicate.
 */
export function robotsTxt(): string {
  return `User-agent: *\nDisallow: /previews/\n\nSitemap: ${SITE_ROOT}sitemap.xml\n`;
}

/**
 * Pages the site wants indexed, absolute. Index pages are listed by their
 * directory with a trailing slash, the form the canonical links use.
 */
export function sitemapXml(pages: Iterable<string>): string {
  const locations = [...new Set([...pages].map(publicUrl))].sort();
  const entries = locations.map((location) => `  <url><loc>${esc(location)}</loc></url>`);
  return `<?xml version="1.0" encoding="UTF-8"?>\n<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">\n${entries.join("\n")}\n</urlset>\n`;
}

/** The public address of a generated file, in the canonical form. */
export function publicUrl(relative: string): string {
  const posix = relative.split(path.sep).join("/");
  const canonical = posix === "index.html" ? "" : posix.endsWith("/index.html") ? posix.slice(0, -"index.html".length) : posix;
  return new URL(canonical, SITE_ROOT).toString();
}
