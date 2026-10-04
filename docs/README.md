# Cloning proof wiki

Open [index.html](index.html) in a browser. The complete generated site works
offline, including search, mathematical display, all 27 named manuscript
results, chapter guides, the [dependency map](dependencies.html), and the
982 audited Lean module pages. The map connects twelve proof
stages with labeled ingredient arrows, a distinct comparison benchmark, and
Lean evidence. Stage selection highlights direct ingredients and uses; all
guides, results, and evidence also remain readable without JavaScript.

[Paper → Lean proof](correspondence.html) connects numbered paper statements,
their argument locations, guide chapters, and compiled proof endpoints. The
guide combines main-text sections and appendices in an editorial reading order;
guide numbers differ from paper section numbers. Each chapter and every proof
step display paper references. The sidebar keeps only the main navigation.
External paper links point to arXiv v1; the guide and Lean source remain bundled.

## Rebuild and check

Run from the repository root with Python 3.10 or newer:

    python3 tools/docs-site/build.py
    python3 tools/docs-site/build.py --check

The builder uses only the Python standard library. It writes only docs/.
--check writes nothing and fails if generated output is stale, an editorial
pointer is missing or ambiguous, a manuscript label is missing, an internal
HTML or Markdown link or HTML anchor is broken, or the Lean sources differ
from the recorded audit.
It does not execute Lean or replace the project’s existing proof audit.

Author English explanations and paper references in docs-src/guides.json.
Every chapter needs its paper locations and every step needs paper_labels.
The frozen paper determines section and shared theorem numbering, including
remarks. tools/docs-site/paper.py reads these counters; docs-src/paper.json
records the reviewed arXiv v1 headings/fragments and retrieved HTML hash.
The build rejects mismatched numbers, missing paper references, and bad pointers.
data/paper-correspondence.json contains the resolved result correspondence.
Author the curated dependency
roadmap in docs-src/dependencies.json. Its stage IDs must match the guides;
ingredient arrows must be acyclic and every edge must have an audited Lean
pointer with an explanation. It describes proof stages, not a complete
proof-term reference graph. Download its resolved data at data/dependencies.json.
Maintain named-result
correspondence in formalization/PROOF_MAP.md. Never edit generated HTML.
The generator and original visual assets live in tools/docs-site/.
The downloaded proof map preserves the original prose and rewrites its links
to the paper on arXiv, offline source pages, and verification evidence.

Exact source is authoritative. Statement excerpts may inherit section variables,
instances, and namespaces; full linked source pages preserve all this context.
The source declaration index excludes ambiguous names and generated constants;
all referenced endpoints must still resolve uniquely against the compiled
AXIOM_REPORT inventory. The recorded full audit covers generated constants too.

The audit snapshot is verification/kernel-compatible-pass, completed
2026-10-04T05:54:37.522297+00:00. manifest.json records input hashes and all
validated guide/map declarations. data/audit-summary.json copies key evidence;
the complete original evidence remains in formalization/verification/.

## Static hosting

The directory is suitable for GitHub Pages at a repository subpath. Every local
URL is relative; there are no runtime API calls, CDNs, or web-font dependencies.
This directory does not enable hosting and does not imply the site is published.
To enable branch-based GitHub Pages, choose Deploy from a branch → main → /docs
in repository Settings → Pages after the generated files have been pushed.

## Assets and provenance

The page organization is inspired by the Fermat’s Last Theorem proof wiki:
https://tianyipeng.github.io/fermats-last-theorem/
https://github.com/anthropics/fermats-last-theorem/tree/main/html

The Python generator, CSS, and application JavaScript are original for this
repository. KaTeX’s minified distribution and MIT license are vendored from
anthropics/fermats-last-theorem/html/assets/vendor/katex (retrieved 2026-10-04).
KaTeX renders native MathML only, so no KaTeX CSS or font assets are required.
The exact bundled bytes are hashed in manifest.json. See
assets/vendor/katex/LICENSE and assets/vendor/katex/README.md.
