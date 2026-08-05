import type { MarkedExtension, Tokens } from "marked";
import { esc } from "./html.js";
import type { SiteModel } from "./model.js";

export type CrossrefKind = "submission" | "concept" | "statement" | "proof";
export interface ResolvedCrossref { kind: CrossrefKind; href: string }

function resolveCrossref(model: SiteModel, target: string, rootRel: string): ResolvedCrossref | undefined {
  const submission = model.submissions.find((s) => s.record.id === target);
  if (submission) return { kind: "submission", href: `${rootRel}${target}/index.html` };
  const concept = model.conceptHome.get(target);
  if (concept) return { kind: "concept", href: `${rootRel}${concept.output.id}/${concept.concept.id}.html` };
  const statement = model.statementHome.get(target);
  if (statement) return { kind: "statement", href: `${rootRel}${statement.output.id}/${statement.concept.id}.html#s-${target}` };
  const proof = model.proofHome.get(target);
  if (proof) return { kind: "proof", href: `${rootRel}${proof.output.id}/${proof.proof.id}.html` };
  return undefined;
}

interface XrefToken { type: "xref"; raw: string; target: string; label: string }

export function crossrefExtension(model: SiteModel, rootRel: string, linked = true): MarkedExtension {
  return {
    extensions: [{
      name: "xref",
      level: "inline",
      start(src: string) { return src.indexOf("[["); },
      tokenizer(src: string): XrefToken | undefined {
        const match = /^\[\[([A-Za-z0-9_.']+)(?:\|([^\]\n]+))?\]\]/.exec(src);
        if (!match) return undefined;
        return { type: "xref", raw: match[0], target: match[1]!, label: match[2] ?? match[1]! };
      },
      renderer(rawToken: Tokens.Generic) {
        const token = rawToken as XrefToken;
        const resolved = resolveCrossref(model, token.target, rootRel);
        const label = esc(token.label);
        if (!linked) return `<code>${label}</code>`;
        return resolved
          ? `<a class="xref xref-${resolved.kind}" href="${esc(resolved.href)}"><code>${label}</code></a>`
          : `<span class="xref xref-broken" title="unresolved reference"><code>${label}</code></span>`;
      },
    }],
  };
}
