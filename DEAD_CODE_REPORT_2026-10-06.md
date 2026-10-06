# Dead code sweep — 2026-10-06

Starting commit: `76dbf1c9bae42525ef635e61a7dd203e3d6d5b18`.
This sweep precedes the elaboration baseline; its removals are not counted as
elaboration improvements.

## Lean

All 994 project modules are reachable from `All` (982 implementation modules,
the `Cloning` facade, `All`, and ten result entrypoints). The import graph has
2,990 local edges and no duplicate direct imports. All 121 explicit private
declarations were examined conservatively.

Removed the six-line private theorem `GeneralCoherentMixture.pure_nonneg`.
Its only source occurrence was its declaration; it had no attributes, public
result index, or wiki pointer. The required full baseline build validates this
deletion. A transient compiled-reference probe was stopped without a result;
no compiled-reference conclusion is claimed here.

Retained public theorems with no textual callers: they are part of the
mathematical API. Retained 316 result-index `#check` commands. Retained repeated
options in sibling namespaces because those namespace boundaries reset them.
No `sorry`, `admit`, or standalone example was found in proof code.

The sweep identified 1,276 transitive-redundant import edges, including 930 in
the public facade and 117 in result indices. These are not dead declarations;
removal requires a measured elaboration benefit and a successful compile.

## Tooling and generated website

Removed the unused Nanoda `sys` import, the unused shared-audit `run_native`
argument, the unused wiki-page `toc` argument, and four unused CSS rules.
All 1,030 generated HTML pages and the dynamic JavaScript contain no matching
nodes for those CSS rules. Regenerated HTML changes only the stylesheet cache
hash. Pinned checker revisions and immutable verification records are preserved.

Validation: 38 wiki tests, 14 verification-wrapper tests, 13 shared-audit tests,
and eight Nanoda guard tests passed; deterministic wiki rebuild/check and
`git diff --check` passed. Subsequent source cleanup requires fresh current
verification evidence, which will be recorded after the elaboration pass.
