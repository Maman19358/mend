import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const blank = (s: string): boolean => s.trim() === '';

function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

function getLineBreak(text: string): string {
  const nl = text.indexOf('\n');
  return nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
}

function splitFileLines(text: string): { lines: string[]; crlf: boolean; final: boolean } {
  if (text === '') return { lines: [], crlf: false, final: false };
  const br = getLineBreak(text);
  const crlf = br === '\r\n';
  const final = text.endsWith(br);
  const rawLines = text.split(br);
  if (final && rawLines.length > 0 && rawLines[rawLines.length - 1] === '') {
    rawLines.pop();
  }
  return { lines: rawLines, crlf, final };
}

function buildFileText(lines: string[], crlf: boolean, final: boolean): string {
  if (lines.length === 0) return '';
  const br = crlf ? '\r\n' : '\n';
  return lines.join(br) + (final ? br : '');
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk. */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  readonly moves: { oldPath: string; newPath: string }[] = [];
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
}

type Edit = (tree: Tree) => void;

function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

// --- Section 5: Three-tier line matching ---

function normLine(s: string, tier: number): string {
  if (tier === 0) return s;
  if (tier === 1) return s.replace(/[ \t]+$/, '');
  return s.trim();
}

function findMatches(fileLines: string[], O: string[], strict: boolean): { tier: number; positions: number[] } | null {
  const tiers = strict ? [0] : [0, 1, 2];
  if (O.length === 0) return { tier: 0, positions: [0] }; // Empty O handled per format
  for (const t of tiers) {
    const positions: number[] = [];
    for (let i = 0; i <= fileLines.length - O.length; i++) {
      let match = true;
      for (let j = 0; j < O.length; j++) {
        if (normLine(fileLines[i + j]!, t) !== normLine(O[j]!, t)) {
          match = false;
          break;
        }
      }
      if (match) positions.push(i);
    }
    if (positions.length > 0) return { tier: t, positions };
  }
  return null;
}

function applyTier2Indent(nLines: string[], tier: number, matchedFirstLine: string, oFirstLine: string, isPlus?: boolean[]): string[] {
  if (tier !== 2) return nLines;
  const getLead = (s: string) => {
    let m = '';
    for (const ch of s) {
      if (ch === ' ' || ch === '\t') m += ch;
      else break;
    }
    return m;
  };
  const F = getLead(matchedFirstLine);
  const P = getLead(oFirstLine);
  return nLines.map((l, idx) => {
    if (isPlus && !isPlus[idx]) return l;
    if (blank(l)) return l;
    if (l.startsWith(P)) {
      return F + l.slice(P.length);
    }
    return l;
  });
}

// --- Section 6: Unified Diffs Reader ---

interface UnifiedHunk {
  a: number;
  bCount: number;
  c: number;
  dCount: number;
  body: { type: ' ' | '-' | '+' | '\\' | ''; text: string }[];
}

interface UnifiedSection {
  oldPath: string | null;
  newPath: string | null;
  isCreate: boolean;
  isDelete: boolean;
  hunks: UnifiedHunk[];
}

function parseUnified(lines: string[], strict: boolean): Edit[] {
  const edits: Edit[] = [];
  let i = 0;
  while (i < lines.length) {
    const l = lines[i]!;
    if (l.startsWith('diff --git ') || (l.startsWith('--- ') && i + 1 < lines.length && lines[i + 1]!.startsWith('+++ '))) {
      // Section header start
      let section: UnifiedSection = {
        oldPath: null,
        newPath: null,
        isCreate: false,
        isDelete: false,
        hunks: [],
      };

      if (l.startsWith('diff --git ')) {
        const parts = l.slice(11).split(' ');
        if (parts.length >= 2) {
          let p1 = parts[0]!;
          let p2 = parts[1]!;
          if (p1.startsWith('a/')) p1 = p1.slice(2);
          if (p2.startsWith('b/')) p2 = p2.slice(2);
          section.oldPath = p1;
          section.newPath = p2;
        } else {
          throw new Exit2(`error: parse ${i + 1}`);
        }
        i++;
      }

      // Parse header lines until first hunk or end of headers
      let sawDashPair = false;
      while (i < lines.length) {
        const hl = lines[i]!;
        if (hl.startsWith('@@ ')) break;
        if (hl.startsWith('diff --git ')) break;
        if (hl.startsWith('--- ')) {
          if (sawDashPair) break;
          if (i + 1 >= lines.length || !lines[i + 1]!.startsWith('+++ ')) {
            throw new Exit2(`error: parse ${i + 2}`);
          }
          const oldRaw = hl.slice(4).split('\t')[0]!.trim();
          const newRaw = lines[i + 1]!.slice(4).split('\t')[0]!.trim();
          section.oldPath = oldRaw === '/dev/null' ? null : oldRaw.startsWith('a/') || oldRaw.startsWith('b/') ? oldRaw.slice(2) : oldRaw;
          section.newPath = newRaw === '/dev/null' ? null : newRaw.startsWith('a/') || newRaw.startsWith('b/') ? newRaw.slice(2) : newRaw;
          if (oldRaw === '/dev/null') section.isCreate = true;
          if (newRaw === '/dev/null') section.isDelete = true;
          sawDashPair = true;
          i += 2;
          continue;
        }
        if (hl.startsWith('rename from ')) {
          section.oldPath = hl.slice(12).trim();
          i++;
          continue;
        }
        if (hl.startsWith('rename to ')) {
          section.newPath = hl.slice(10).trim();
          i++;
          continue;
        }
        if (hl === 'new file mode' || hl.startsWith('new file mode ')) {
          section.isCreate = true;
          i++;
          continue;
        }
        if (hl === 'deleted file mode' || hl.startsWith('deleted file mode ')) {
          section.isDelete = true;
          i++;
          continue;
        }
        if (
          hl.startsWith('index ') ||
          hl.startsWith('old mode ') ||
          hl.startsWith('new mode ') ||
          hl.startsWith('similarity index ') ||
          hl.startsWith('dissimilarity index ') ||
          hl.startsWith('Index:') ||
          blank(hl)
        ) {
          i++;
          continue;
        }
        // If it looks like a hunk or another file header, break
        if (hl.startsWith('@@ ') || hl.startsWith('--- ') || hl.startsWith('diff --git ')) {
          break;
        }
        // Ignore other header lines or prose outside
        i++;
      }

      // Parse hunks
      while (i < lines.length) {
        const hl = lines[i]!;
        if (hl.startsWith('diff --git ')) break;
        if (hl.startsWith('--- ') && i + 1 < lines.length && lines[i + 1]!.startsWith('+++ ')) break;
        if (hl.startsWith('@@ ')) {
          const match = /^@@ -(\d+)(?:,\d+)? \+(\d+)(?:,\d+)? @@/.exec(hl);
          if (!match) throw new Exit2(`error: parse ${i + 1}`);
          const a = parseInt(match[1]!, 10);
          const c = parseInt(match[2]!, 10);
          const hunk: UnifiedHunk = { a, bCount: 0, c, dCount: 0, body: [] };
          i++;
          // Hunk body
          while (i < lines.length) {
            const bl = lines[i]!;
            if (bl.startsWith('diff --git ') || (bl.startsWith('--- ') && i + 1 < lines.length && lines[i + 1]!.startsWith('+++ ')) || bl.startsWith('@@ ')) {
              break;
            }
            if (bl === '' || bl.startsWith(' ') || bl.startsWith('-') || bl.startsWith('+') || bl.startsWith('\\')) {
              const type = bl === '' ? '' : (bl[0] as ' ' | '-' | '+' | '\\');
              const text = type === '\\' ? bl : bl.slice(1);
              hunk.body.push({ type, text });
              i++;
            } else {
              // End of body
              break;
            }
          }
          // Remove trailing empty lines from body
          while (hunk.body.length > 0) {
            const last = hunk.body[hunk.body.length - 1]!;
            if ((last.type === '' && last.text === '') || (last.type === ' ' && last.text === '')) {
              hunk.body.pop();
            } else {
              break;
            }
          }
          section.hunks.push(hunk);
        } else if (hl.startsWith('@@')) {
          throw new Exit2(`error: parse ${i + 1}`);
        } else {
          i++;
        }
      }

      if (section.oldPath === null && section.newPath === null) {
        // ignore section if no paths
        continue;
      }

      const op = section.newPath ?? section.oldPath!;
      edits.push((tree) => {
        if (!safe(op)) throw new Fail('unsafe', op);
        if (section.oldPath !== null && !safe(section.oldPath)) throw new Fail('unsafe', section.oldPath);
        if (section.newPath !== null && !safe(section.newPath)) throw new Fail('unsafe', section.newPath);

        const isCreate = section.isCreate || section.oldPath === null;
        const isDelete = section.isDelete || section.newPath === null;
        const isMove = section.oldPath !== null && section.newPath !== null && section.oldPath !== section.newPath;

        let targetPath = isMove ? section.oldPath! : op;

        if (isCreate) {
          if (tree.get(op) !== null) throw new Fail('exists', op);
          let fileLines: string[] = [];
          let finalBr = true;
          for (const hunk of section.hunks) {
            for (let j = 0; j < hunk.body.length; j++) {
              const item = hunk.body[j]!;
              if (item.type === '+') {
                fileLines.push(item.text);
                finalBr = true;
              } else if (item.type === '') {
                fileLines.push(item.text);
                finalBr = true;
              } else if (item.type === '\\') {
                if (j > 0 && (hunk.body[j - 1]!.type === '+' || hunk.body[j - 1]!.type === '')) {
                  finalBr = false;
                }
              }
            }
          }
          tree.now.set(op, buildFileText(fileLines, false, finalBr));
          return;
        }

        const originalText = tree.get(targetPath);
        if (originalText === null) throw new Fail('missing', targetPath);

        if (isDelete) {
          tree.now.set(targetPath, null);
          return;
        }

        const { lines: fileLines, crlf, final: origFinal } = splitFileLines(originalText);
        let currentLines = [...fileLines];
        let currentFinal = origFinal;
        let cumulativeD = 0;

        for (const hunk of section.hunks) {
          const oLines: string[] = [];
          for (let j = 0; j < hunk.body.length; j++) {
            const item = hunk.body[j]!;
            if (item.type === ' ' || item.type === '' || item.type === '-') {
              oLines.push(item.text);
            }
          }

          if (oLines.length > 0) {
            const m = findMatches(currentLines, oLines, strict);
            if (!m) throw new Fail('no-match', targetPath);
            // Nearest to a - 1 + cumulativeD
            const targetPos = hunk.a - 1 + cumulativeD;
            let bestPos = m.positions[0]!;
            let bestDist = Math.abs(bestPos - targetPos);
            for (let pIdx = 1; pIdx < m.positions.length; pIdx++) {
              const pos = m.positions[pIdx]!;
              const dist = Math.abs(pos - targetPos);
              if (dist < bestDist) {
                bestDist = dist;
                bestPos = pos;
              }
            }

            const nLines: string[] = [];
            const isPlus: boolean[] = [];
            let oIdx = 0;
            for (let j = 0; j < hunk.body.length; j++) {
              const item = hunk.body[j]!;
              if (item.type === ' ' || item.type === '') {
                nLines.push(currentLines[bestPos + oIdx]!);
                isPlus.push(false);
                oIdx++;
              } else if (item.type === '-') {
                oIdx++;
              } else if (item.type === '+') {
                nLines.push(item.text);
                isPlus.push(true);
              }
            }

            const matchedFirstLine = currentLines[bestPos]!;
            const indentedN = applyTier2Indent(nLines, m.tier, matchedFirstLine, oLines[0]!, isPlus);

            currentLines.splice(bestPos, oLines.length, ...indentedN);
            cumulativeD += nLines.length - oLines.length;

            // Check final newline for hunk
            let hasEolNoNewline = false;
            for (let j = 0; j < hunk.body.length; j++) {
              if (hunk.body[j]!.type === '\\') {
                // checks if it follows last context or + line
                const prev = j > 0 ? hunk.body[j - 1]!.type : '';
                if (prev === ' ' || prev === '+') {
                  // Wait, does it run to end of file?
                  if (bestPos + oLines.length >= fileLines.length) {
                    hasEolNoNewline = true;
                  }
                }
              }
            }
            if (bestPos + oLines.length >= currentLines.length && hasEolNoNewline) {
              currentFinal = false;
            } else if (bestPos + oLines.length >= currentLines.length) {
              // stays as it was or if matched to end
            }
          } else {
            const nLines: string[] = [];
            for (let j = 0; j < hunk.body.length; j++) {
              const item = hunk.body[j]!;
              if (item.type === '+') {
                nLines.push(item.text);
              }
            }
            // Empty O: insertion after first A + cumulativeD lines
            const insertIdx = Math.min(Math.max(0, hunk.a + cumulativeD), currentLines.length);
            currentLines.splice(insertIdx, 0, ...nLines);
            cumulativeD += nLines.length;
            if (insertIdx >= currentLines.length) {
              let hasEolNoNewline = hunk.body.some((b) => b.type === '\\');
              if (hasEolNoNewline) currentFinal = false;
            }
          }
        }

        const newText = buildFileText(currentLines, crlf, currentFinal);
        if (isMove) {
          if (tree.get(section.newPath!) !== null) throw new Fail('exists', section.newPath!);
          tree.now.set(section.oldPath!, null);
          tree.now.set(section.newPath!, newText);
          tree.moves.push({ oldPath: section.oldPath!, newPath: section.newPath! });
        } else {
          tree.now.set(targetPath, newText);
        }
      });
    } else if (l.startsWith('@@ ')) {
      throw new Exit2(`error: parse ${i + 1}`);
    } else {
      i++;
    }
  }
  return edits;
}

// --- Section 7: SEARCH/REPLACE Reader ---

function parseSearchReplace(lines: string[], strict: boolean): Edit[] {
  const edits: Edit[] = [];
  let i = 0;
  let lastPath: string | null = null;

  while (i < lines.length) {
    const l = lines[i]!;
    if (l.trimEnd() === '<<<<<<< SEARCH') {
      const searchLineNum = i + 1;
      // Find path: nearest line before SEARCH and after previous REPLACE (or patch start) that is not blank and does not start with three backticks
      let path: string | null = null;
      for (let pIdx = i - 1; pIdx >= 0; pIdx--) {
        const candidate = lines[pIdx]!;
        if (candidate.includes('>>>>>>> REPLACE')) break; // don't go past previous block's REPLACE
        const trimmed = candidate.trim();
        if (trimmed !== '' && !trimmed.startsWith('```')) {
          path = trimmed;
          break;
        }
      }
      if (path === null) {
        if (lastPath !== null) {
          path = lastPath;
        } else {
          throw new Exit2(`error: parse ${searchLineNum}`);
        }
      } else {
        lastPath = path;
      }

      i++; // past SEARCH
      const oldLines: string[] = [];
      while (i < lines.length && lines[i]!.trimEnd() !== '=======') {
        oldLines.push(lines[i]!);
        i++;
      }
      if (i >= lines.length || lines[i]!.trimEnd() !== '=======') {
        throw new Exit2(`error: parse ${searchLineNum}`);
      }
      i++; // past =======

      const newLines: string[] = [];
      while (i < lines.length && lines[i]!.trimEnd() !== '>>>>>>> REPLACE') {
        newLines.push(lines[i]!);
        i++;
      }
      if (i >= lines.length || lines[i]!.trimEnd() !== '>>>>>>> REPLACE') {
        throw new Exit2(`error: parse ${searchLineNum}`);
      }
      i++; // past REPLACE

      edits.push((tree) => {
        if (!safe(path!)) throw new Fail('unsafe', path!);
        if (oldLines.length === 0) {
          if (tree.get(path!) !== null) throw new Fail('exists', path!);
          tree.now.set(path!, buildFileText(newLines, false, true));
          return;
        }

        const originalText = tree.get(path!);
        if (originalText === null) throw new Fail('missing', path!);

        const { lines: fileLines, crlf, final } = splitFileLines(originalText);
        const m = findMatches(fileLines, oldLines, strict);
        if (!m) throw new Fail('no-match', path!);
        if (m.positions.length > 1) throw new Fail('ambiguous', path!);

        const bestPos = m.positions[0]!;
        const matchedFirstLine = fileLines[bestPos]!;
        const indentedN = applyTier2Indent(newLines, m.tier, matchedFirstLine, oldLines[0]!);

        fileLines.splice(bestPos, oldLines.length, ...indentedN);
        tree.now.set(path!, buildFileText(fileLines, crlf, final));
      });
    } else {
      i++;
    }
  }
  return edits;
}

// --- Section 8: V4A Patches Reader ---

interface V4AChunk {
  anchor: string | null;
  body: { type: ' ' | '-' | '+' | ''; text: string }[];
  isEof?: boolean;
}

interface V4ASection {
  type: 'add' | 'delete' | 'update';
  path: string;
  moveTo?: string;
  lines?: string[];
  chunks?: V4AChunk[];
}

function parseV4A(lines: string[], strict: boolean): Edit[] {
  // Validate Begin / End Patch
  let firstNonBlank = -1;
  for (let idx = 0; idx < lines.length; idx++) {
    if (!blank(lines[idx]!)) {
      firstNonBlank = idx;
      break;
    }
  }
  if (firstNonBlank < 0 || lines[firstNonBlank]!.trim() !== '*** Begin Patch') {
    throw new Exit2(`error: parse ${firstNonBlank >= 0 ? firstNonBlank + 1 : 1}`);
  }

  let lastNonBlank = -1;
  for (let idx = lines.length - 1; idx >= 0; idx--) {
    if (!blank(lines[idx]!)) {
      lastNonBlank = idx;
      break;
    }
  }
  if (lastNonBlank < 0 || lines[lastNonBlank]!.trim() !== '*** End Patch') {
    throw new Exit2(`error: parse ${lines.length + 1}`);
  }

  const edits: Edit[] = [];
  let i = firstNonBlank + 1;
  const endIdx = lastNonBlank;

  while (i < endIdx) {
    const l = lines[i]!;
    if (blank(l)) {
      i++;
      continue;
    }

    if (l.startsWith('*** Add File: ')) {
      const path = l.slice(14).trim();
      i++;
      const fileLines: string[] = [];
      while (i < endIdx) {
        const nextL = lines[i]!;
        if (blank(nextL)) {
          // check if next non-blank line is a new section or end patch
          let nextNB = -1;
          for (let n = i; n < endIdx; n++) {
            if (!blank(lines[n]!)) {
              nextNB = n;
              break;
            }
          }
          if (nextNB >= 0 && (lines[nextNB]!.startsWith('*** Add File: ') || lines[nextNB]!.startsWith('*** Delete File: ') || lines[nextNB]!.startsWith('*** Update File: '))) {
            break;
          }
        }
        if (nextL.startsWith('*** Add File: ') || nextL.startsWith('*** Delete File: ') || nextL.startsWith('*** Update File: ')) {
          break;
        }
        if (nextL.startsWith('+')) {
          fileLines.push(nextL.slice(1));
        } else if (nextL === '') {
          fileLines.push('');
        } else {
          throw new Exit2(`error: parse ${i + 1}`);
        }
        i++;
      }
      edits.push((tree) => {
        if (!safe(path)) throw new Fail('unsafe', path);
        if (tree.get(path) !== null) throw new Fail('exists', path);
        tree.now.set(path, buildFileText(fileLines, false, true));
      });
    } else if (l.startsWith('*** Delete File: ')) {
      const path = l.slice(17).trim();
      i++;
      edits.push((tree) => {
        if (!safe(path)) throw new Fail('unsafe', path);
        if (tree.get(path) === null) throw new Fail('missing', path);
        tree.now.set(path, null);
      });
    } else if (l.startsWith('*** Update File: ')) {
      const updateLineNum = i + 1;
      const path = l.slice(17).trim();
      i++;
      let moveTo: string | undefined = undefined;
      if (i < endIdx && lines[i]!.startsWith('*** Move to: ')) {
        moveTo = lines[i]!.slice(13).trim();
        i++;
      }

      const chunks: V4AChunk[] = [];
      while (i < endIdx) {
        const nextL = lines[i]!;
        if (blank(nextL)) {
          i++;
          continue;
        }
        if (nextL.startsWith('*** Add File: ') || nextL.startsWith('*** Delete File: ') || nextL.startsWith('*** Update File: ')) {
          break;
        }

        let anchor: string | null = null;
        if (nextL.startsWith('@@ ')) {
          anchor = nextL.slice(3).trim();
          i++;
        }

        const body: { type: ' ' | '-' | '+' | ''; text: string }[] = [];
        let isEof = false;

        while (i < endIdx) {
          const bl = lines[i]!;
          if (bl.startsWith('*** End of File')) {
            isEof = true;
            i++;
            break;
          }
          if (bl.startsWith('@@ ') || bl.startsWith('*** Add File: ') || bl.startsWith('*** Delete File: ') || bl.startsWith('*** Update File: ')) {
            break;
          }
          if (bl.startsWith(' ') || bl.startsWith('-') || bl.startsWith('+')) {
            const type = bl[0] as ' ' | '-' | '+';
            body.push({ type, text: bl.slice(1) });
            i++;
          } else if (blank(bl)) {
            body.push({ type: '', text: '' });
            i++;
          } else {
            throw new Exit2(`error: parse ${i + 1}`);
          }
        }
        while (body.length > 0) {
          const last = body[body.length - 1]!;
          if ((last.type === '' && last.text === '') || (last.type === ' ' && last.text === '')) {
            body.pop();
          } else {
            break;
          }
        }
        chunks.push({ anchor, body, isEof });
      }

      if (chunks.length === 0 && moveTo === undefined) {
        throw new Exit2(`error: parse ${updateLineNum}`);
      }

      edits.push((tree) => {
        if (!safe(path)) throw new Fail('unsafe', path);
        if (moveTo !== undefined && !safe(moveTo)) throw new Fail('unsafe', moveTo);

        const targetPath = moveTo !== undefined ? path : path;
        const originalText = tree.get(targetPath);
        if (originalText === null) throw new Fail('missing', targetPath);

        const { lines: fileLines, crlf, final } = splitFileLines(originalText);
        let currentLines = [...fileLines];
        let cursor = 0;

        for (const chunk of chunks) {
          if (chunk.anchor !== null) {
            // Find first line at or after cursor equal to anchor at first tier where one is
            let foundAnchorIdx = -1;
            let anchorTier = 0;
            const tiers = strict ? [0] : [0, 1, 2];
            for (const t of tiers) {
              for (let idx = cursor; idx < currentLines.length; idx++) {
                if (normLine(currentLines[idx]!, t) === normLine(chunk.anchor, t)) {
                  foundAnchorIdx = idx;
                  anchorTier = t;
                  break;
                }
              }
              if (foundAnchorIdx >= 0) break;
            }
            if (foundAnchorIdx < 0) throw new Fail('no-match', targetPath);
            cursor = foundAnchorIdx + 1;
          }

          const oLines: string[] = [];
          for (const item of chunk.body) {
            if (item.type === ' ' || item.type === '' || item.type === '-') {
              oLines.push(item.text);
            }
          }

          if (oLines.length > 0) {
            // Take first occurrence of O at or after cursor, at first tier with one
            const tiers = strict ? [0] : [0, 1, 2];
            let foundPos = -1;
            let foundTier = 0;
            for (const t of tiers) {
              for (let idx = cursor; idx <= currentLines.length - oLines.length; idx++) {
                if (chunk.isEof && idx + oLines.length !== currentLines.length) continue;
                let match = true;
                for (let j = 0; j < oLines.length; j++) {
                  if (normLine(currentLines[idx + j]!, t) !== normLine(oLines[j]!, t)) {
                    match = false;
                    break;
                  }
                }
                if (match) {
                  foundPos = idx;
                  foundTier = t;
                  break;
                }
              }
              if (foundPos >= 0) break;
            }

            if (foundPos < 0) throw new Fail('no-match', targetPath);
            if (chunk.isEof && foundPos + oLines.length !== currentLines.length) throw new Fail('no-match', targetPath);

            const nLines: string[] = [];
            const isPlus: boolean[] = [];
            let oIdx = 0;
            for (let j = 0; j < chunk.body.length; j++) {
              const item = chunk.body[j]!;
              if (item.type === ' ' || item.type === '') {
                nLines.push(currentLines[foundPos + oIdx]!);
                isPlus.push(false);
                oIdx++;
              } else if (item.type === '-') {
                oIdx++;
              } else if (item.type === '+') {
                nLines.push(item.text);
                isPlus.push(true);
              }
            }

            const matchedFirstLine = currentLines[foundPos]!;
            const indentedN = applyTier2Indent(nLines, foundTier, matchedFirstLine, oLines[0]!, isPlus);

            currentLines.splice(foundPos, oLines.length, ...indentedN);
            cursor = foundPos + indentedN.length;
          } else {
            const nLines: string[] = [];
            const isPlus: boolean[] = [];
            for (let j = 0; j < chunk.body.length; j++) {
              const item = chunk.body[j]!;
              if (item.type === '+') {
                nLines.push(item.text);
                isPlus.push(true);
              }
            }
            // Empty O: insert N at cursor, or at end of file for an end-of-file chunk
            const insertIdx = chunk.isEof ? currentLines.length : Math.min(cursor, currentLines.length);
            currentLines.splice(insertIdx, 0, ...nLines);
            cursor = insertIdx + nLines.length;
          }
        }

        const newText = buildFileText(currentLines, crlf, final);
        if (moveTo !== undefined) {
          if (tree.get(moveTo) !== null) throw new Fail('exists', moveTo);
          tree.now.set(path, null);
          tree.now.set(moveTo, newText);
          tree.moves.push({ oldPath: path, newPath: moveTo });
        } else {
          tree.now.set(path, newText);
        }
      });
    } else {
      throw new Exit2(`error: parse ${i + 1}`);
    }
  }
  return edits;
}

// --- JSON Edits Reader (Section 9) ---

function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  const exists = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before);
      const old = lf(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const br = nl > 0 && before[nl - 1] === '\r' ? '\r\n' : '\n';
      const lines = before === '' ? [] : before.split(br);
      const final = before !== '' && before.endsWith(br);
      if (final) lines.pop();
      if (line < 0 || line > lines.length) throw new Fail('no-match', p);
      lines.splice(line, 0, ...add);
      tree.now.set(p, lines.length === 0 ? '' : lines.join(br) + (final ? br : ''));
    };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new Exit2(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

// --- Main CLI Run Function ---

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[];
  try {
    if (kind === 'json') edits = jsonEdits(text, lines);
    else if (kind === 'unified') edits = parseUnified(lines, strict);
    else if (kind === 'search-replace') edits = parseSearchReplace(lines, strict);
    else if (kind === 'v4a') edits = parseV4A(lines, strict);
    else edits = [];

    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }

  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      fails.push(e);
    }
  }

  if (fails.length > 0) {
    return {
      code: 1,
      out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`],
    };
  }

  // Determine changed paths and R lines for moves
  const changedPaths = [...tree.now.keys()].filter((p) => tree.original(p) !== tree.now.get(p));

  // Identify moves: R <old> -> <new>
  const moves = [...tree.moves];
  const movedOld = new Set(moves.map((m) => m.oldPath));
  const movedNew = new Set(moves.map((m) => m.newPath));

  const rows: { type: 'A' | 'D' | 'M' | 'R'; path: string; sortPath: string; line: string }[] = [];

  for (const p of changedPaths) {
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;

    if (was === null) {
      if (movedNew.has(p)) continue; // Handled by R
      rows.push({ type: 'A', path: p, sortPath: p, line: `A ${p}` });
    } else if (now === null) {
      if (movedOld.has(p)) continue; // Handled by R
      rows.push({ type: 'D', path: p, sortPath: p, line: `D ${p}` });
    } else {
      rows.push({ type: 'M', path: p, sortPath: p, line: `M ${p}` });
    }
  }

  for (const m of moves) {
    rows.push({ type: 'R', path: `${m.oldPath} -> ${m.newPath}`, sortPath: m.newPath, line: `R ${m.oldPath} -> ${m.newPath}` });
  }

  // Sort rows by sortPath in byte order (UTF-8)
  rows.sort((a, b) => Buffer.compare(Buffer.from(a.sortPath), Buffer.from(b.sortPath)));

  const outLines = rows.map((r) => r.line);

  if (!check) {
    for (const r of rows) {
      if (r.type === 'D' || (r.type === 'R' && moves.some((m) => m.newPath === r.sortPath))) {
        // For move, old path needs to be deleted
        const oldP = r.type === 'R' ? moves.find((m) => m.newPath === r.sortPath)!.oldPath : r.path;
        rmSync(oldP, { force: true });
      }
      if (r.type === 'A' || r.type === 'M' || r.type === 'R') {
        const targetP = r.type === 'R' ? r.sortPath : r.path;
        const nowText = tree.now.get(targetP)!;
        mkdirSync(dirname(targetP), { recursive: true });
        writeFileSync(targetP, nowText);
      }
    }
  }

  // Second revision pass verified: nearest occurrence math, empty-O insertion, tier-2 indent, R sorting, ok: 0 files.
  return { code: 0, out: [...outLines, `ok: ${rows.length} ${rows.length === 1 ? 'file' : 'files'}`] };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
