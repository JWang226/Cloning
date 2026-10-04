# Offline proof wiki generator

From the repository root:

    python3 tools/docs-site/build.py
    python3 tools/docs-site/build.py --check

Python 3.10 or newer is the only build requirement. Open docs/index.html
directly in a browser; the bundled proof pages need no server or network connection.

The generator reads:

- docs-src/guides.json: editorial chapter explanations and explicit proof pointers.
- formalization/PROOF_MAP.md: manuscript-to-Lean correspondence.
- The frozen reference snapshot identified in formalization/SOURCE.json: the 27 named manuscript statements.
- The snapshot selected by formalization/verification/latest.json.
- Comparator and Nanoda status summaries and any linked archived run records.
- Every audited implementation module and the original static assets here.

It checks that the Lean inputs still match the audit's recorded hashes, resolves
all guide/map pointers against actual source declarations and compiled
AXIOM_REPORT entries, requires exact agreement between the manuscript's 27
labels and the named-result map, and validates every generated local link and
HTML anchor, including links in the downloadable Markdown map. The --check mode
additionally compares deterministic output
byte-for-byte and writes nothing.

Only docs/ is generated. A marker prevents replacement of an unrelated
nonempty directory. Edit the generator/assets or the editorial inputs, then
rebuild; do not hand-edit generated pages. No Lean, audit, or reference source
is changed or re-executed.

The site includes exact complete .lean source copies, line-anchored source
pages, a local JavaScript search index, chapter guides, named results, scope
notes, and a verification summary. Statement excerpts are exact source slices
without proof bodies; linked modules preserve inherited section variables,
instances, and namespace context.

The downloadable proof map keeps the source map's prose and rewrites its links
to the [paper](https://arxiv.org/abs/2609.35986), exact source pages, and verification evidence.
The generator leaves the repository's formalization/PROOF_MAP.md unmodified.

Checker status is rendered from its saved summary. A pass requires a hash-matched
archived full-run record, a matching audit binding and tool lock, the checker
success marker, and the complete declared scope. Nanoda also requires its archived
binding.json and agreement between exported and checked declaration counts.
Preparation, readiness, failed runs, and incomplete runs never display a pass.

KaTeX 0.18.4 is bundled under its MIT license and renders native MathML, so no
font files or external assets are necessary. See assets/vendor/katex/.

The generated .nojekyll supports GitHub Pages. To publish via repository
settings, choose **Deploy from a branch → main → /docs**. Generating the files
does not enable Pages or claim that a public URL is live.
