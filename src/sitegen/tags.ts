import type { SiteSubmission } from "./model.js";

export interface SubmissionTag {
  key: string;
  label: string;
  submissionIds: string[];
}

export interface SubmissionTagIndex {
  tags: SubmissionTag[];
  bySubmission: Map<string, string[]>;
}

interface Token {
  key: string;
  label: string;
}

interface Candidate {
  key: string;
  labels: Map<string, number>;
  submissions: Map<string, number>;
  titleSubmissions: Set<string>;
  words: string[];
  occurrences: number;
  score: number;
}

const WORD_ALIASES: Record<string, string> = {
  bounds: "bound",
  classes: "class",
  colourability: "colorability",
  colourable: "colorable",
  coloured: "colored",
  colouring: "coloring",
  colourings: "coloring",
  colours: "color",
  components: "component",
  definitions: "definition",
  denseness: "dense",
  graphs: "graph",
  lemmas: "lemma",
  minors: "minor",
  neighbourhood: "neighborhood",
  neighbourhoods: "neighborhood",
  neighborhoods: "neighborhood",
  numbers: "number",
  pairs: "pair",
  partitions: "partition",
  paths: "path",
  proofs: "proof",
  roots: "root",
  sentences: "sentence",
  sets: "set",
  systems: "system",
  theorems: "theorem",
  transductions: "transduction",
  tuples: "tuple",
};

const EDGE_WORDS = new Set([
  "a", "all", "almost", "an", "and", "are", "as", "at", "below", "between",
  "by", "constructive", "for", "from", "general", "has", "have", "in", "into",
  "is", "of", "on", "or", "the", "to", "under", "with", "without",
]);

const GENERIC_WORDS = new Set([
  "approach", "bound", "class", "constructive", "definition", "experiment",
  "finite", "general", "lemma", "method", "number", "proof", "result", "set",
  "system", "theorem", "time",
]);

const UNHELPFUL_UNIGRAMS = new Set([
  ...GENERIC_WORDS,
  "admissible", "almost", "bounded", "coloring", "connected", "degree", "edge",
  "fixed", "linear", "local", "minor", "most", "neighborhood", "order", "pair",
  "sparse", "strong", "two", "vertex",
]);

const UNHELPFUL_PHRASES = new Set([
  "almost linear",
  "almost linear neighborhood",
  "dense graph",
  "linear neighborhood",
]);

const THREE_WORD_ENDINGS = new Set(["complexity", "lemma", "machine", "theorem"]);

const MAX_TAGS = 18;

function canonicalWord(value: string): string {
  const word = value.normalize("NFKD").replace(/\p{M}/gu, "").toLocaleLowerCase();
  return WORD_ALIASES[word] ?? word;
}

function tokens(value: string): Token[] {
  // TeX commands describe notation rather than topics; leaving a space keeps
  // phrases on either side from being accidentally joined together.
  const prose = value.replace(/\\[A-Za-z]+/g, " ");
  return [...prose.matchAll(/[\p{L}\p{N}]+/gu)]
    .map((match) => ({ key: canonicalWord(match[0]), label: match[0] }))
    .filter((token) => token.key.length >= 2 && !/^\d+$/.test(token.key));
}

function candidateScore(candidate: Candidate): number {
  const documentFrequency = candidate.submissions.size;
  const weight = [...candidate.submissions.values()].reduce((sum, value) => sum + value, 0);
  const genericWords = candidate.words.filter((word) => GENERIC_WORDS.has(word)).length;
  return documentFrequency * 24
    + Math.log2(weight + 1) * 8
    + candidate.titleSubmissions.size * 6
    + (candidate.words.length - 1) * 5
    - genericWords * 4;
}

function sameSubmissions(a: Candidate, b: Candidate): boolean {
  if (a.submissions.size !== b.submissions.size) return false;
  return [...a.submissions.keys()].every((id) => b.submissions.has(id));
}

function nestedPhrase(a: Candidate, b: Candidate): boolean {
  const aWords = ` ${a.words.join(" ")} `;
  const bWords = ` ${b.words.join(" ")} `;
  return aWords.includes(bWords) || bWords.includes(aWords);
}

function displayLabel(candidate: Candidate): string {
  const [label = candidate.key] = [...candidate.labels]
    .sort((a, b) => b[1] - a[1] || a[0].localeCompare(b[0]))[0] ?? [];
  return label.charAt(0).toLocaleUpperCase() + label.slice(1);
}

/**
 * Build a compact, deterministic topic index from the archive's own words.
 * Submission titles carry more weight than concept titles, while repeated
 * concept vocabulary lets related submissions meet under one tag. No archive
 * record is changed and no hand-maintained subject taxonomy can drift from it.
 */
export function submissionTagIndex(submissions: SiteSubmission[]): SubmissionTagIndex {
  const candidates = new Map<string, Candidate>();
  const listed = submissions.filter((submission) => submission.output);

  for (const submission of listed) {
    const output = submission.output!;
    const references = [
      { value: output.manifest.title, weight: 5, title: true },
      ...output.concepts.map((concept) => ({ value: concept.title, weight: 1, title: false })),
    ];
    for (const reference of references) {
      const words = tokens(reference.value);
      for (let width = 1; width <= 3; width += 1) {
        for (let start = 0; start + width <= words.length; start += 1) {
          const phrase = words.slice(start, start + width);
          if (width === 3 && !THREE_WORD_ENDINGS.has(phrase.at(-1)!.key)) continue;
          if (EDGE_WORDS.has(phrase[0]!.key) || EDGE_WORDS.has(phrase.at(-1)!.key)) continue;
          if (width === 1 && UNHELPFUL_UNIGRAMS.has(phrase[0]!.key)) continue;
          const key = phrase.map((word) => word.key).join(" ");
          if (UNHELPFUL_PHRASES.has(key)) continue;
          const label = phrase.map((word) => word.label).join(" ");
          const candidate = candidates.get(key) ?? {
            key,
            labels: new Map(),
            submissions: new Map(),
            titleSubmissions: new Set(),
            words: phrase.map((word) => word.key),
            occurrences: 0,
            score: 0,
          };
          candidate.labels.set(label, (candidate.labels.get(label) ?? 0) + reference.weight);
          candidate.submissions.set(
            submission.record.id,
            (candidate.submissions.get(submission.record.id) ?? 0) + reference.weight,
          );
          candidate.occurrences += 1;
          if (reference.title) candidate.titleSubmissions.add(submission.record.id);
          candidates.set(key, candidate);
        }
      }
    }
  }

  const ranked = [...candidates.values()]
    .filter((candidate) => candidate.occurrences >= 2 || candidate.titleSubmissions.size > 0)
    .map((candidate) => ({ ...candidate, score: candidateScore(candidate) }))
    .sort((a, b) => b.score - a.score
      || b.words.length - a.words.length
      || a.key.localeCompare(b.key));

  const selected: Candidate[] = [];
  const add = (candidate: Candidate): boolean => {
    const sameResults = selected.filter((existing) => sameSubmissions(existing, candidate));
    if (sameResults.some((existing) => nestedPhrase(existing, candidate)) || sameResults.length >= 2) return false;
    selected.push(candidate);
    return true;
  };

  // Give every submission one strong local phrase before adding archive-wide
  // vocabulary. This prevents a prolific submission from occupying the strip
  // with many related terms and keeps small submissions discoverable.
  for (const submission of listed) {
    const id = submission.record.id;
    const local = ranked.filter((candidate) => candidate.submissions.has(id));
    const phrases = local.filter((candidate) => candidate.words.length > 1);
    const primary = (phrases.length ? phrases : local)
      .sort((a, b) => {
        const localA = (a.submissions.get(id) ?? 0) * 12
          + (a.titleSubmissions.has(id) ? 30 : 0)
          + a.words.length * 5
          - a.submissions.size * 2;
        const localB = (b.submissions.get(id) ?? 0) * 12
          + (b.titleSubmissions.has(id) ? 30 : 0)
          + b.words.length * 5
          - b.submissions.size * 2;
        return localB - localA || b.score - a.score || a.key.localeCompare(b.key);
      })[0];
    if (primary) add(primary);
  }

  for (const candidate of ranked) {
    if (selected.length >= MAX_TAGS) break;
    add(candidate);
  }

  const tags = selected
    .map((candidate) => ({
      key: candidate.key,
      label: displayLabel(candidate),
      submissionIds: [...candidate.submissions.keys()].sort(),
    }))
    .sort((a, b) => b.submissionIds.length - a.submissionIds.length
      || a.label.localeCompare(b.label));
  const bySubmission = new Map(listed.map((submission) => [submission.record.id, [] as string[]]));
  for (const tag of tags)
    for (const id of tag.submissionIds) bySubmission.get(id)?.push(tag.key);
  for (const keys of bySubmission.values()) keys.sort();
  return { tags, bySubmission };
}
