#!/usr/bin/env python3
"""Build and check an offline proof wiki from the audited Lean source snapshot.

Only docs/ is written. This program uses the Python standard library and never
invokes Lean or changes its verification evidence. Run from any directory.
"""
from __future__ import annotations

import argparse
import hashlib
import html
from html.parser import HTMLParser
import json
from pathlib import Path, PurePosixPath
import re
import sys
from urllib.parse import unquote, urlsplit, urlunsplit
from paper import RESULT_ARGUMENTS, paper_structure

ROOT = Path(__file__).resolve().parents[2]
FORMAL = ROOT / "formalization"
OUT = ROOT / "docs"
ASSETS = Path(__file__).parent / "assets"
GITHUB = "https://github.com/JWang226/Cloning/blob/main/"
ARXIV = "https://arxiv.org/abs/2609.35986"
GENERATED_MARKER = ".proof-wiki-generated"
TICK = chr(96)
MARKDOWN_LINK = re.compile(r"\[[^\]\n]*\]\(([^)\s]+)\)")
MARKDOWN_REFERENCE = re.compile(r"(?m)^ {0,3}\[[^\]\n]+\]:\s*(?:<([^>\n]+)>|(\S+))")


def esc(value):
    return html.escape(str(value), quote=True)


def sha(data):
    if isinstance(data, str):
        data = data.encode()
    return hashlib.sha256(data).hexdigest()


def slug(value):
    return re.sub(r"[^a-z0-9]+", "-", value.lower()).strip("-")


def offline_proof_map(text):
    """Link the paper on arXiv and keep proof/evidence links offline."""
    pages = {
        "PROGRESS.md": "../verification.html",
        "verification/latest.json": "../data/audit-summary.json",
    }

    def rewrite(match):
        url = urlsplit(match[1])
        path = unquote(url.path)
        if path == "cloning.tex" or path.endswith("/reference/cloning.tex") or path == "reference/cloning.tex":
            return "[paper on arXiv](" + ARXIV + ")"
        if url.scheme or url.netloc or not url.path:
            return match[0]
        target = pages.get(path, url.path)
        if path.startswith("Cloning/") and path.endswith(".lean"):
            module = path[:-len(".lean")].replace("/", ".")
            target = "../source/" + module + ".html"
        href = urlunsplit(("", "", target, url.query, url.fragment))
        return match[0][:match.start(1) - match.start()] + href + ")"

    return MARKDOWN_LINK.sub(rewrite, text)


def checker_verdict(name, summary, record, audit_sha256, project_constants,
                    lock_sha256, binding=None):
    """A preparation record can never become a successful checker verdict."""
    status = summary.get("status", "not_run")
    pending = {
        "prepared_not_run": "Prepared; full check not run",
        "ready_not_run": "Ready; full check not run",
        "not_run": "Full check not run",
        "blocked": "Blocked; no completed certificate",
        "running": "Running; no completed certificate",
        "interrupted": "Interrupted; no completed certificate",
        "failed": "Failed; no completed certificate",
    }
    if status != "passed":
        return pending.get(status, "Unverified status; no completed certificate")

    def require(condition, message):
        if not condition:
            raise ValueError(f"{name} recorded success is not verified: {message}")

    require(summary.get("source_audit_sha256") == audit_sha256, "summary audit binding differs")
    require(record is not None and record.get("status") == "passed", "archived full run did not pass")
    if name == "comparator":
        for data in (summary, record):
            require(data.get("comparator_executed") is True, "Comparator was not executed")
            require(data.get("comparator_verdict") == "Your solution is okay!", "success marker missing")
        require(summary.get("claims") == 27, "statement scope is not all 27 named results")
        require(record.get("source_audit_sha256") == audit_sha256, "run audit binding differs")
        require(record.get("lock_sha256") == lock_sha256, "run tool lock differs")
        require(summary.get("mode") == record.get("mode") and record.get("mode") in
                ("trusted-local-no-sandbox", "linux-landrun"), "run mode differs or is unknown")
        return "Passed: 27 statements and proof dependencies, Lean kernel replay"

    require(name == "nanoda", "unknown checker")
    for data in (summary, record):
        require(data.get("independent_kernel_check") == "passed", "independent kernel check did not pass")
        require(data.get("project_declarations") == project_constants, "project declaration scope differs")
    exported = summary.get("exported_declarations")
    require(type(exported) is int and exported >= project_constants, "exported declaration count missing")
    require(record.get("checked_declarations") == exported, "checked and exported counts differ")
    require(record.get("mode") == "run" and record.get("phase") == "complete" and
            record.get("inputs_unchanged") is True, "full check or stability gates did not complete")
    require(record.get("tools_lock_sha256") == lock_sha256, "run tool lock differs")
    require(record.get("source_binding") == "matched", "run source binding did not match")
    require(binding is not None and binding.get("run_sha256") == audit_sha256 and
            binding.get("project_declarations") == project_constants and
            binding.get("source_binding") == "matched", "archived audit binding differs")
    return f"Passed: {project_constants:,} project roots; {exported:,} declarations checked"


def inline(value):
    """Small, escaped inline subset; never execute HTML from editorial inputs."""
    pieces = re.split(r"(\x60[^\x60]+\x60|\*\*[^*]+\*\*)", str(value))
    result = []
    for piece in pieces:
        if piece.startswith(TICK) and piece.endswith(TICK):
            result.append("<code>" + esc(piece[1:-1]) + "</code>")
        elif piece.startswith("**") and piece.endswith("**"):
            result.append("<strong>" + esc(piece[2:-2]) + "</strong>")
        else:
            result.append(esc(piece))
    return "".join(result)


def paragraphs(value):
    if isinstance(value, list):
        return "".join("<p>" + inline(x) + "</p>" for x in value)
    return "".join("<p>" + inline(x) + "</p>" for x in str(value).split("\n\n") if x.strip())


def items(values):
    return "<ul>" + "".join("<li>" + inline(x) + "</li>" for x in values) + "</ul>"


def lean_mask(text):
    """Hide nested Lean comments and strings without moving source offsets."""
    out = list(text)
    i, depth, string = 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                out[i:i + 2] = "  "
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                out[i:i + 2] = "  "
                depth -= 1
                i += 2
            else:
                if text[i] != "\n":
                    out[i] = " "
                i += 1
        elif string:
            if text[i] == "\\":
                out[i] = " "
                if i + 1 < len(text):
                    if text[i + 1] != "\n":
                        out[i + 1] = " "
                    i += 2
                else:
                    i += 1
            else:
                if text[i] == '"':
                    string = False
                if text[i] != "\n":
                    out[i] = " "
                i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            if end < 0:
                end = len(text)
            out[i:end] = " " * (end - i)
            i = end
        elif text.startswith("/-", i):
            out[i:i + 2] = "  "
            depth = 1
            i += 2
        elif text[i] == '"':
            out[i] = " "
            string = True
            i += 1
        else:
            i += 1
    return "".join(out)


DECL = re.compile(
    r"(?m)^[ \t]*(?:@\[[^\n]*?\]\s*)*"
    r"(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
    r"(?P<kind>theorem|lemma|def|abbrev|structure|class|inductive|opaque)\s+"
    r"(?P<name>[^\s:({\[]+)"
)


def statement_end(mask, start, limit):
    depth = 0
    bindings = 0
    for token in re.finditer(r":=|\b(?:let|letI|have|where)\b|[()[\]{}]", mask[start:limit]):
        value = token[0]
        if value in ("(", "{", "["):
            depth += 1
        elif value in (")", "}", "]"):
            depth -= 1
        elif depth == 0 and value in ("let", "letI", "have"):
            bindings += 1
        elif depth == 0 and value == ":=":
            if bindings:
                bindings -= 1
            else:
                return start + token.start()
        elif depth == 0 and value == "where":
            return start + token.start()
    return limit


class Wiki:
    def __init__(self):
        self.files = {}
        self.inputs = {}
        self.search = []
        self.declarations = {}
        self.modules = {}
        self.pointer_uses = []
        self.read(Path(__file__).with_name("paper.py"))
        self.latest = self.read_json(FORMAL / "verification/latest.json")
        self.audit_dir = FORMAL / self.latest["directory"]
        self.run = self.read_json(self.audit_dir / "run.json")
        if sha((self.audit_dir / "run.json").read_bytes()) != self.latest["run_sha256"]:
            raise ValueError("Latest verification pointer has a different run.json hash")
        self.audit = self.read_json(self.audit_dir / "verification.json")
        self.lean_version = self.read(FORMAL / "lean-toolchain").strip()
        if self.run["status"] != "passed" or self.audit["axiom_audit"] != "passed":
            raise ValueError("The selected audit is not a passing audit")
        for file, expected in self.run["input_sha256"].items():
            source = FORMAL / file
            if not source.is_file() or sha(source.read_bytes()) != expected:
                raise ValueError(f"Source no longer matches the compiled audit: {file}")
        for file in ("AXIOMS.txt", "verification.json"):
            expected = self.run["evidence_sha256"].get(file)
            if expected and sha((self.audit_dir / file).read_bytes()) != expected:
                raise ValueError(f"Audit evidence hash differs: {file}")
        self.inventory = []
        for line in self.read(self.audit_dir / "AXIOMS.txt").splitlines():
            if line.startswith("AXIOM_REPORT "):
                self.inventory.append(json.loads(line[len("AXIOM_REPORT "):]))
        self.index_sources()
        self.manuscript = self.parse_manuscript()
        self.paper = self.read_json(ROOT / "docs-src/paper.json")
        self.validate_paper()
        self.results = self.parse_map()
        expected = set(self.manuscript)
        if len(expected) != 27 or set(self.results) != expected:
            raise ValueError(f"Named-result mismatch: manuscript={len(expected)}, map={len(self.results)}, "
                             f"difference={expected.symmetric_difference(self.results)}")
        self.guides = self.read_json(ROOT / "docs-src/guides.json")
        self.chapters = self.guides["chapters"]
        chapter_ids = [c["id"] for c in self.chapters]
        if len(set(chapter_ids)) != len(chapter_ids) or any(slug(x) != x for x in chapter_ids):
            raise ValueError("Chapter ids must be unique lowercase URL slugs")
        self.validate_guides()
        self.dependencies = self.read_json(ROOT / "docs-src/dependencies.json")
        self.validate_dependencies()

    def read(self, path):
        data = path.read_bytes()
        self.inputs[path.relative_to(ROOT).as_posix()] = sha(data)
        return data.decode()

    def read_json(self, path):
        return json.loads(self.read(path))

    def put(self, path, content):
        if path in self.files:
            raise ValueError("Duplicate output: " + path)
        self.files[path] = content.encode() if isinstance(content, str) else content

    def index_sources(self):
        by_module = {}
        for row in self.inventory:
            if not row.get("private"):
                by_module.setdefault(row["module"], []).append(row)
        for module in sorted(by_module):
            path = FORMAL / (module.replace(".", "/") + ".lean")
            text = self.read(path)
            mask = lean_mask(text)
            candidates = list(DECL.finditer(mask))
            module_info = {"name": module, "file": path.relative_to(ROOT).as_posix(),
                           "text": text, "declarations": [],
                           "url": "source/" + module + ".html"}
            for ix, match in enumerate(candidates):
                bare = match["name"]
                matches = [r for r in by_module[module]
                           if r["name"] == bare or r["name"].endswith("." + bare)]
                # Same suffix in separate namespaces is ambiguous: pointers must
                # not silently choose one. Such declarations remain in full source.
                if len(matches) != 1:
                    continue
                row = matches[0]
                start = match.start()
                line = text.count("\n", 0, start) + 1
                limit = candidates[ix + 1].start() if ix + 1 < len(candidates) else len(text)
                end = statement_end(mask, match.end("name"), limit)
                # A displayed statement is the exact source slice; inherited
                # variables and namespace context remain available in the module.
                statement = text[start:end].rstrip()
                declaration = {**row, "file": module_info["file"], "line": line,
                               "source_name": bare, "statement": statement,
                               "url": module_info["url"] + "#L" + str(line)}
                self.declarations[row["name"]] = declaration
                module_info["declarations"].append(declaration)
            self.modules[module] = module_info

    def resolve(self, name, file=None, strict=True):
        if file:
            file = PurePosixPath(file).as_posix()
            if not file.startswith("formalization/"):
                file = "formalization/" + file
        candidates = [d for n, d in self.declarations.items()
                      if (n == name or n.endswith("." + name)) and (not file or d["file"] == file)]
        if not candidates and file and not strict:
            candidates = [d for n, d in self.declarations.items()
                          if n == name or n.endswith("." + name)]
        if len(candidates) != 1:
            raise ValueError(f"Unresolved or ambiguous declaration {name!r} in {file!r}: "
                             + str([d["name"] for d in candidates]))
        d = candidates[0]
        self.pointer_uses.append({"name": d["name"], "file": d["file"], "line": d["line"]})
        return d

    def parse_manuscript(self):
        text = self.read(FORMAL / "reference/cloning.tex")
        sections, numbered = paper_structure(text)
        self.paper_sections = {s["number"]: s for s in sections}
        self.paper_labels = {s["label"]: s for s in sections}
        self.paper_labels.update({"section:" + s["number"]: s for s in sections})
        pattern = re.compile(
            r"\\begin\{(theorem|lemma|proposition|corollary)\}(?:\[([^\]]+)\])?"
            r"(.*?)\\end\{\1\}", re.S)
        found = {}
        for match in pattern.finditer(text):
            labels = re.findall(r"\\label\{((?:thm|lem|prop|cor):[^}]+)\}", match[3])
            for label in labels:
                found[label] = {"kind": match[1], "title": (match[2] or label).replace("--", "–"),
                                "tex": match[0], "line": text.count("\n", 0, match.start()) + 1,
                                **numbered[label],
                                "argument_sections": RESULT_ARGUMENTS.get(label, [numbered[label]["section"]])}
        return found

    def validate_paper(self):
        if (self.paper["paper_url"] != ARXIV or self.paper["version"] != "v1" or
                self.paper["html_url"] != "https://arxiv.org/html/2609.35986v1"):
            raise ValueError("Paper links must use the reviewed arXiv v1")
        expected = [{k: s[k] for k in ("number", "title", "anchor")} for s in self.paper_sections.values()]
        if self.paper["sections"] != expected:
            raise ValueError("Paper section metadata differs from the frozen manuscript")
        if set(self.paper["results"]) != set(self.manuscript):
            raise ValueError("Paper result metadata differs from the frozen manuscript")
        for label, result in self.manuscript.items():
            reviewed = self.paper["results"][label]
            if any(reviewed[k] != result[k] for k in ("number", "citation", "anchor", "section")):
                raise ValueError("Paper result numbering or anchor differs: " + label)
            if any(number not in self.paper_sections for number in result["argument_sections"]):
                raise ValueError("Unknown paper argument section: " + label)

    def paper_reference(self, label):
        if label in self.manuscript:
            result = self.manuscript[label]
            return {"text": result["citation"], "url": self.paper["html_url"] + "#" + result["anchor"]}
        if label in self.paper_labels:
            section = self.paper_labels[label]
            number = section["number"]
            prefix = "Appendix " if len(number) == 1 and number.isalpha() else "§"
            return {"text": prefix + number + " · " + section["title"],
                    "url": self.paper["html_url"] + "#" + section["anchor"]}
        raise ValueError("Unknown paper reference " + label)

    def paper_link(self, label, compact=False):
        reference = self.paper_reference(label)
        text = reference["text"].split(" · ")[0] if compact else reference["text"]
        context = f' title="{esc(reference["text"])}"' if compact else ""
        return f'<a href="{esc(reference["url"])}"{context}>{esc(text)}</a>'

    def parse_map(self):
        content = self.read(FORMAL / "PROOF_MAP.md")
        self.map_text = content
        section = ""
        results = {}
        for line in content.splitlines():
            if line.startswith("## "):
                section = line[3:]
            if section not in ("Main named theorems", "Named auxiliary statements"):
                continue
            cells = [x.strip() for x in line.strip().strip("|").split("|")]
            if len(cells) != 3:
                continue
            labels = re.findall(r"\x60((?:thm|lem|prop|cor):[^\x60]+)\x60", cells[0])
            if not labels:
                continue
            label = labels[0]
            result = results.setdefault(label, {**self.manuscript[label], "label": label,
                                                "parts": [], "url": "results/" + slug(label) + ".html"})
            pointers = []
            cell = cells[1]
            links = list(re.finditer(r"\[([^\]]+)\]\(([^)]+\.lean)\)", cell))
            prev = 0
            for link in links:
                pending = cell[prev:link.start()]
                for name in re.findall(r"\x60([^\x60]+)\x60", pending):
                    d = self.resolve(name, link[2], strict=False)
                    if d["name"] not in {x["name"] for x in pointers}:
                        pointers.append(d)
                prev = link.end()
            for name in re.findall(r"\x60([^\x60]+)\x60", cell[prev:]):
                d = self.resolve(name)
                if d["name"] not in {x["name"] for x in pointers}:
                    pointers.append(d)
            if not pointers:
                raise ValueError("No Lean endpoints for " + label)
            result["parts"].append({"label": cells[0].replace(TICK, ""),
                                    "scope": cells[2], "pointers": pointers})
        return results

    def validate_guides(self):
        covered_results = set()
        for chapter in self.chapters:
            for field in ("title", "summary", "assumptions", "steps", "results", "limitations"):
                if field not in chapter:
                    raise ValueError(f"Missing guide field {field} in {chapter['id']}")
            for step in chapter["steps"]:
                step["_pointers"] = [self.resolve(x["name"], x["file"]) for x in step.get("lean", [])]
                if not step.get("paper_labels"):
                    raise ValueError("Guide step needs a paper reference: " + chapter["id"])
                for label in step["paper_labels"]:
                    self.paper_reference(label)
            paper = chapter.get("paper", {})
            if not paper.get("sections") or not paper.get("explanation"):
                raise ValueError("Guide needs its paper correspondence: " + chapter["id"])
            for location in paper["sections"]:
                if location.get("role") not in ("statement", "argument", "supporting", "discussion"):
                    raise ValueError("Unknown paper correspondence role")
                if location["label"] not in self.paper_labels:
                    raise ValueError("Unknown guide paper section " + location["label"])
            for result in chapter["results"]:
                result["_pointer"] = self.resolve(result["name"], result["file"])
                if result.get("label", "").startswith(("thm:", "lem:", "prop:", "cor:")):
                    if result["label"] not in self.results:
                        raise ValueError("Unknown manuscript result label " + result["label"])
            labels = chapter.get("manuscript_labels", [])
            if not isinstance(labels, list) or any(not isinstance(x, str) for x in labels):
                raise ValueError("Guide manuscript_labels must be a list of labels: " + chapter["id"])
            if len(labels) != len(set(labels)):
                raise ValueError("Duplicate manuscript result in guide " + chapter["id"])
            chapter_names = {p["name"] for step in chapter["steps"] for p in step["_pointers"]}
            chapter_names.update(result["_pointer"]["name"] for result in chapter["results"])
            for label in labels:
                if label not in self.results:
                    raise ValueError("Unknown manuscript result label " + label)
                result_names = {p["name"] for part in self.results[label]["parts"] for p in part["pointers"]}
                if not chapter_names.intersection(result_names):
                    raise ValueError(f"Guide {chapter['id']} has no corresponding Lean endpoint for {label}")
            covered_results.update(labels)
        missing = set(self.results) - covered_results
        if missing:
            raise ValueError("Named results missing a proof guide: " + ", ".join(sorted(missing)))

    def validate_dependencies(self):
        """Validate an editorial stage graph and its audited source evidence."""
        nodes = self.dependencies["nodes"]
        ids = [n["id"] for n in nodes]
        expected = {c["id"] for c in self.chapters}
        if len(ids) != len(set(ids)) or set(ids) != expected:
            raise ValueError("Dependency stages must match the proof guides exactly once")
        if self.dependencies.get("default_stage") not in expected:
            raise ValueError("Unknown default dependency stage")
        self.dependency_nodes = {n["id"]: n for n in nodes}
        self.dependency_chapters = {c["id"]: c for c in self.chapters}
        outgoing = {n: [] for n in ids}
        seen = set()
        for edge in self.dependencies["edges"]:
            source, target = edge["from"], edge["to"]
            if source not in expected or target not in expected:
                raise ValueError("Unknown dependency edge stage")
            if source == target or (source, target) in seen:
                raise ValueError("Self or duplicate dependency edge")
            seen.add((source, target))
            kind = edge.get("kind", "ingredient")
            if kind not in ("ingredient", "comparison"):
                raise ValueError("Unknown dependency edge kind")
            if not edge.get("label") or not edge.get("evidence"):
                raise ValueError("Dependency edges require a contribution and Lean evidence")
            if kind == "ingredient":
                outgoing[source].append(target)
            for evidence in edge["evidence"]:
                if not evidence.get("note"):
                    raise ValueError("Dependency evidence requires an explanation")
                evidence["_pointer"] = self.resolve(evidence["name"], evidence["file"])
        visiting, done = set(), set()

        def visit(node):
            if node in visiting:
                raise ValueError("Ingredient dependency graph contains a cycle")
            if node in done:
                return
            visiting.add(node)
            for target in outgoing[node]:
                visit(target)
            visiting.remove(node)
            done.add(node)

        for node in ids:
            visit(node)

    def page(self, path, title, body, active="", toc="", extra_assets=()):
        depth = len(PurePosixPath(path).parts) - 1
        prefix = "../" * depth
        nav = [
            ("index.html", "Overview", "overview"),
            ("correspondence.html", "Paper ↔ Lean", "correspondence"),
            ("guides/index.html", "Proof guide", "guides"),
            ("dependencies.html", "Dependency map", "dependencies"),
            ("results/index.html", "27 named results", "results"),
            ("source/index.html", "Lean source", "source"),
            ("verification.html", "Verification", "verification"),
            ("scope.html", "Scope & conventions", "scope"),
        ]
        nav_html = "".join(
            f'<a class="nav-link{" active" if key == active else ""}" href="{prefix}{url}"'
            + (' aria-current="page"' if key == active else "") + f'>{esc(label)}</a>'
            for url, label, key in nav)
        extra_head = "".join(
            f'<link rel="stylesheet" href="{prefix}assets/{esc(asset)}">' if asset.endswith(".css")
            else f'<script defer src="{prefix}assets/{esc(asset)}"></script>'
            for asset in extra_assets)
        html_text = f'''<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<meta name="description" content="An offline guide to the Lean formalization of asymptotic mixed-state quantum cloning. Exact source, proof routes, and audited scope.">
<title>{esc(title)} · Cloning proof wiki</title>
<link rel="stylesheet" href="{prefix}assets/site.css">
<script>window.PROOF_ROOT={json.dumps(prefix)};</script>
<script defer src="{prefix}assets/vendor/katex/katex.min.js"></script>
<script defer src="{prefix}assets/search-index.js"></script>
<script defer src="{prefix}assets/site.js"></script>
{extra_head}
</head><body><a class="skip-link" href="#main">Skip to content</a>
<div class="site-shell"><aside class="sidebar" id="site-navigation">
<a class="brand" href="{prefix}index.html"><span class="brand-mark">C</span><span>Cloning<span class="small muted">A Lean proof wiki</span></span></a>
<nav aria-label="Main navigation"><div class="nav-section">Explore</div>{nav_html}</nav>
<div class="sidebar-footer"><span class="badge">Lean 4</span><p>Manuscript → proof → source</p>
<a href="https://github.com/JWang226/Cloning">Repository ↗</a></div></aside>
<div class="main-shell"><header class="topbar">
<button id="nav-toggle" class="button secondary" aria-controls="site-navigation" aria-expanded="false" aria-label="Toggle navigation">Menu</button>
<div class="search-wrap"><label class="sr-only" for="site-search">Search the proof wiki</label>
<input id="site-search" type="search" placeholder="Search results, concepts, or Lean names…" autocomplete="off" aria-controls="search-results" aria-expanded="false" role="combobox" aria-autocomplete="list">
<div id="search-results" class="search-results" role="listbox" hidden></div></div>
<span class="small muted topbar-label">Offline · exact source</span></header>
<main id="main" class="content">{body}</main>
<footer class="footer">English guides explain the argument. Lean source and its hypotheses determine the formal claims.
<a href="{prefix}verification.html">Audit evidence</a> · <a href="{prefix}scope.html">Scope</a></footer>
</div></div></body></html>'''
        self.put(path, html_text)

    def math(self, tex, display=False):
        return f'<span class="{"math-display" if display else "math-inline"}" data-tex="{esc(tex)}" data-display="{str(display).lower()}">{esc(tex)}</span>'

    def declaration(self, d, prefix="../", compact=False):
        file = d["file"]
        source = prefix + d["url"]
        external = GITHUB + file + "#L" + str(d["line"])
        statement_id = "lean-" + slug(d["name"])
        # Exact repeated pointers on a page must not create duplicate HTML ids.
        self.snippet_serial = getattr(self, "snippet_serial", 0) + 1
        statement_id += "-" + str(self.snippet_serial)
        excerpt = (f'<div class="code-wrap"><pre class="code-block" id="{statement_id}"><code>'
                   + esc(d["statement"]) + '</code></pre></div>')
        if compact:
            excerpt = '<details><summary>Exact Lean statement excerpt</summary>' + excerpt + "</details>"
        return (f'<article class="declaration"><div class="declaration-header">'
                f'<a href="{esc(source)}"><code>{esc(d["name"])}</code></a>'
                f'<span class="badge">{esc(d["kind"])}</span></div>'
                f'<p class="small muted">{esc(PurePosixPath(file).name)} · line {d["line"]}'
                f' · <a href="{esc(source)}">Full source and context</a>'
                f' · <a href="{esc(external)}">GitHub ↗</a>'
                f' · <button class="copy-button" data-copy-target="{statement_id}" aria-label="Copy Lean excerpt">Copy</button></p>'
                + excerpt + "</article>")

    def result_card(self, result, prefix):
        scopes = " ".join(p["scope"] for p in result["parts"])
        search = result["title"] + " " + result["label"] + " " + result["citation"] + " " + scopes
        return (f'<article class="result-card" data-filter-text="{esc(search.lower())}">'
                f'<div class="badges"><span class="badge">{esc(result["citation"])}</span></div>'
                f'<h3><a href="{prefix}{result["url"]}">{esc(result["title"])}</a></h3>'
                f'<p>{inline(scopes)}</p><a class="card-arrow" href="{prefix}{result["url"]}">Read statement & proof pointers →</a></article>')

    def chapter_cards(self, prefix):
        return '<div class="cards">' + "".join(
            f'<a class="card" href="{prefix}guides/{c["id"]}.html"><span class="card-index">{i:02}</span>'
            f'<h3>{esc(c["title"])}</h3><p>{inline(c["summary"])}</p>'
            '<p class="paper-step-location">Paper: ' + ", ".join(
                esc(self.paper_reference(x["label"])["text"].split(" · ")[0]) for x in c["paper"]["sections"]) + '</p>'
            '<span class="card-arrow">Follow the argument →</span></a>'
            for i, c in enumerate(self.chapters, 1)) + "</div>"

    def render_overview(self):
        a = self.audit
        intro = paragraphs(self.guides["intro"]).replace(
            "the paper", f'the <a href="{ARXIV}">paper</a>', 1)
        body = (f'<section class="hero"><div class="eyebrow">Quantum information · formal mathematics</div>'
                f'<h1>{esc(self.guides.get("title", "The proof of mixed-state cloning"))}</h1>'
                f'<div class="lead">{intro}</div>'
                '<div class="actions"><a class="button" href="guides/index.html">Start the proof guide →</a>'
                '<a class="button secondary" href="results/index.html">Browse all 27 results</a>'
                '<a class="button secondary" href="correspondence.html">Paper ↔ Lean correspondence</a>'
                f'<a class="button secondary" href="{ARXIV}">Read the paper on arXiv ↗</a></div></section>'
                '<section class="stats" aria-label="Verification snapshot">'
                f'<div class="stat"><span class="stat-value">27</span><span class="stat-label">named manuscript results</span></div>'
                f'<div class="stat"><span class="stat-value">{a["modules"]:,}</span><span class="stat-label">audited Lean modules</span></div>'
                f'<div class="stat"><span class="stat-value">{a["audited_constants"]:,}</span><span class="stat-label">compiled constants audited</span></div>'
                '<div class="stat"><span class="stat-value">3</span><span class="stat-label">standard logical axioms only</span></div></section>'
                '<section class="callout info"><h2>Paper → Lean proof</h2>'
                '<p>Start with a numbered result in the <a href="correspondence.html">paper-to-Lean table</a>. It points to the paper’s statement and proof sections, the corresponding informal guide, and the compiled Lean declarations. The twelve guide chapters follow the proof ingredients and combine material from the main text and appendices; their numbers differ from the paper’s section numbers.</p>'
                '<p><a href="dependencies.html">The dependency map</a> connects the proof stages and shows the Lean evidence for each contribution.</p>'
                '<p class="small">The English explanation is editorial. It does not replace the hypotheses in Lean. '
                '<a href="scope.html">Read the conventions and open questions →</a></p></section>'
                '<div class="section-heading"><div><div class="eyebrow">The proof route</div><h2>From finite copies to limiting optima</h2></div>'
                '<a href="guides/index.html">All chapters →</a></div>'
                + self.chapter_cards("")
                + '<div class="section-heading"><div><div class="eyebrow">The main conclusions</div><h2>Four theorem families</h2></div>'
                '<a href="results/index.html">All named results →</a></div><div class="cards">'
                + "".join(self.result_card(r, "") for r in list(self.results.values())[:4]) + "</div>"
                '<section class="callout"><h2>What the verification certifies</h2>'
                '<p>The source matches the recorded passing build and full declaration axiom audit. The wiki separately checks that every guide pointer names a compiled declaration at the displayed source location. A successful build does not turn the manuscript’s conjectures into theorems.</p>'
                '<a href="verification.html">Inspect the evidence and reproduce the site →</a></section>')
        self.page("index.html", "Mixed-state cloning", body, "overview")
        self.search.append({"title": "Overview: mixed-state cloning", "subtitle": "Start here", "kind": "Page",
                            "url": "index.html", "text": self.guides["intro"]})

    def render_guides(self):
        body = ('<div class="eyebrow">Read the argument</div><h1>The proof guide</h1>'
                '<p class="lead">These twelve chapters reorganize the paper’s arguments by proof ingredient. A chapter can combine several paper sections and appendices. Guide numbers describe this reading order; paper references retain the paper’s numbering.</p>'
                '<p><a href="../correspondence.html">Find a numbered paper result and its Lean proof →</a></p>'
                '<p><a href="../dependencies.html">See how the stages depend on each other →</a></p>'
                '<h2 id="paper-correspondence">Guide chapters and their paper locations</h2>'
                '<p class="small muted">Section and theorem references link to arXiv v1. Open a guide for the informal steps and their Lean counterparts.</p>'
                '<div class="paper-guide-table" tabindex="0" aria-label="Guide chapter correspondence; scroll horizontally on a narrow screen"><table>'
                '<thead><tr><th>Informal guide</th><th>Where in the paper</th><th>Paper results → Lean</th></tr></thead><tbody>')
        for i, c in enumerate(self.chapters, 1):
            body += (f'<tr><td><a href="{c["id"]}.html"><strong>{i:02} · {esc(c["title"])}</strong></a>'
                     f'<p class="small">{inline(c["paper"]["explanation"])}</p></td><td>'
                     + self.paper_locations(c) + '</td><td>')
            if c.get("manuscript_labels"):
                body += '<ul>' + "".join(f'<li><a href="../{self.results[label]["url"]}">{esc(self.results[label]["citation"])}</a></li>'
                                         for label in c["manuscript_labels"]) + '</ul>'
            else:
                body += '<p class="small">Definitions and discussion; Lean pointers are in the guide.</p>'
            body += '</td></tr>'
        body += '</tbody></table></div>'
        self.page("guides/index.html", "Proof guide", body, "guides")
        for i, c in enumerate(self.chapters):
            steps_toc = "".join(f'<a href="#step-{j}">{j}. {esc(s["title"])}</a>'
                                for j, s in enumerate(c["steps"], 1))
            body = (f'<div class="eyebrow">Proof guide · chapter {i + 1:02} of {len(self.chapters):02}</div>'
                    f'<h1>{esc(c["title"])}</h1><p class="paper-step-location">Paper: '
                    + " · ".join(self.paper_link(label, compact=True) for label in c.get("manuscript_labels", []))
                    + (' · ' if c.get("manuscript_labels") else '')
                    + " · ".join(self.paper_link(x["label"], compact=True) for x in c["paper"]["sections"])
                    + f'</p><p class="lead">{inline(c["summary"])}</p>')
            body += (f'<section class="paper-correspondence" id="paper"><h2>Where this guide fits in the paper</h2>'
                     + paragraphs(c["paper"]["explanation"]) + self.paper_locations(c)
                     + '<p class="small">Guide numbering follows the reading order; the linked sections retain the paper’s numbering.</p>'
                     f'<p class="small"><a href="../dependencies.html#stage-{esc(c["id"])}">This chapter in the dependency map →</a></p></section>')
            body += '<div class="split-layout"><article class="prose">'
            if c.get("statement"):
                body += '<section class="callout"><h2>At a glance</h2>' + self.math(c["statement"], True) + "</section>"
            body += '<section id="assumptions"><h2>Setting and assumptions</h2>' + items(c["assumptions"]) + "</section>"
            for j, step in enumerate(c["steps"], 1):
                body += (f'<section class="step" id="step-{j}"><div class="step-number">{j:02}</div>'
                         f'<h2>{esc(step["title"])}</h2>' + paragraphs(step["explanation"])
                         + '<p class="paper-step-location">Paper: ' + " · ".join(self.paper_link(label) for label in step["paper_labels"]) + '</p>'
                         + "".join(self.declaration(d, compact=True) for d in step["_pointers"]) + "</section>")
            body += '<section id="results"><h2>Results reached in this chapter</h2>'
            for result in c["results"]:
                label = result["label"]
                if label in self.results:
                    body += f'<p><a href="../{self.results[label]["url"]}">{esc(self.results[label]["citation"])} · {esc(self.results[label]["title"])}</a></p>'
                else:
                    body += "<h3>" + esc(label) + "</h3>"
                body += self.declaration(result["_pointer"], compact=True)
            if c.get("manuscript_labels"):
                body += '<h3>Corresponding manuscript statements</h3><ul>' + "".join(
                    f'<li><a href="../{self.results[label]["url"]}">{esc(self.results[label]["citation"])} · {esc(self.results[label]["title"])}</a></li>'
                    for label in c["manuscript_labels"]) + "</ul>"
            body += "</section>"
            if c["limitations"]:
                body += '<section class="callout" id="boundaries"><h2>Scope of this step</h2>' + items(c["limitations"]) + "</section>"
            body += ('</article><aside class="toc" aria-label="On this page"><div class="nav-section">In this chapter</div>'
                     '<a href="#paper">Where in the paper</a><a href="#assumptions">Setting and assumptions</a>' + steps_toc
                     + '<a href="#results">Results reached</a>'
                     + ('<a href="#boundaries">Scope</a>' if c["limitations"] else "") + "</aside></div>")
            body += '<nav class="chapter-prevnext" aria-label="Previous and next chapter">'
            body += (f'<a href="{self.chapters[i - 1]["id"]}.html">← {esc(self.chapters[i - 1]["title"])}</a>'
                     if i else '<a href="index.html">← Guide overview</a>')
            body += (f'<a href="{self.chapters[i + 1]["id"]}.html">{esc(self.chapters[i + 1]["title"])} →</a>'
                     if i + 1 < len(self.chapters) else '<a href="../results/index.html">All named results →</a>')
            body += "</nav>"
            url = "guides/" + c["id"] + ".html"
            self.page(url, c["title"], body, "guides")
            self.search.append({"title": c["title"], "subtitle": f"Chapter {i + 1:02}", "kind": "Guide",
                                "url": url, "text": c["summary"] + " " + c["paper"]["explanation"] + " "
                                + " ".join(self.paper_reference(x["label"])["text"] for x in c["paper"]["sections"])
                                + " " + " ".join(s["explanation"] for s in c["steps"])})

    def paper_locations(self, chapter):
        return '<ul class="paper-location-list">' + "".join(
            f'<li><span class="badge paper-location">{esc(x["role"].title())}</span> {self.paper_link(x["label"])}</li>'
            for x in chapter["paper"]["sections"]) + '</ul>'

    def render_correspondence(self):
        body = ('<div class="eyebrow">Paper → Lean proof</div><h1>From the paper to Lean</h1>'
                '<p class="lead">Find each of the paper’s 27 numbered results, read its informal argument, and inspect the Lean declarations that formalize it.</p>'
                '<p>The paper states its four main theorems in §1.1 and develops their arguments later. The guide combines those sections and appendices into twelve chapters. '
                f'Section and result numbers below refer to <a href="{esc(self.paper["version_url"])}">arXiv v1</a>.</p>'
                '<p><a href="guides/index.html#paper-correspondence">How every guide chapter relates to the paper →</a></p>'
                '<div class="paper-guide-table" tabindex="0" aria-label="Paper to Lean correspondence; scroll horizontally on a narrow screen">'
                '<table><thead><tr><th>Paper statement</th><th>Paper argument</th><th>Informal proof guide</th><th>Lean proof endpoints</th></tr></thead><tbody>')
        records = []
        for result in self.results.values():
            guides = [c for c in self.chapters if result["label"] in c.get("manuscript_labels", [])]
            endpoints = {p["name"]: p for part in result["parts"] for p in part["pointers"]}
            body += (f'<tr id="{slug(result["label"])}"><td>{self.paper_link(result["label"])}'
                     f'<p><a href="{result["url"]}">{esc(result["title"])}</a></p></td><td><ul>'
                     + "".join('<li>' + self.paper_link('section:' + number) + '</li>' for number in result["argument_sections"])
                     + '</ul></td><td><ul>' + "".join(f'<li><a href="guides/{c["id"]}.html">{esc(c["title"])}</a></li>' for c in guides)
                     + '</ul></td><td><ul>' + "".join(f'<li><a href="{esc(p["url"])}"><code>{esc(p["name"])}</code></a></li>' for p in endpoints.values())
                     + '</ul></td></tr>')
            records.append({"label": result["label"], "citation": result["citation"], "title": result["title"],
                            "statement_url": self.paper_reference(result["label"])["url"],
                            "statement_section": result["section"],
                            "argument_sections": [self.paper_reference('section:' + number) for number in result["argument_sections"]],
                            "guide_urls": [f'guides/{c["id"]}.html' for c in guides],
                            "lean": [{k: p[k] for k in ("name", "file", "line", "url")} for p in endpoints.values()]})
        body += ('</tbody></table></div><section class="callout"><h2>How to read the correspondence</h2>'
                 '<p>Paper links locate the statement and its argument. Guide links explain the construction and estimates; Lean links show exact compiled statements and complete proof bodies. '
                 'Result pages record hypotheses and any distinctions between a general paper statement and the concrete formal endpoints.</p>'
                 '<p>The LAN guide describes the constructed Lean witnesses underlying the LAN theorem that the paper obtains from cited work. Discussion of all-density optima and degenerate spectra remains distinct from proved results.</p>'
                 '<a href="data/paper-correspondence.json">Download the correspondence data</a></section>')
        self.page("correspondence.html", "Paper to Lean correspondence", body, "correspondence")
        self.put("data/paper-correspondence.json", json.dumps({"paper_version": self.paper["version_url"],
                 "paper_html": self.paper["html_url"], "source_audit_sha256": self.latest["run_sha256"],
                 "results": records}, indent=2, ensure_ascii=False) + '\n')
        self.search.append({"title": "Paper to Lean correspondence", "subtitle": "Numbered paper statements, informal arguments, and compiled proofs",
                            "kind": "Page", "url": "correspondence.html", "text": "paper sections appendices theorem numbers guide chapters formal proof correspondence"})

    def render_results(self):
        body = ('<div class="eyebrow">Manuscript → Lean</div><h1>All 27 named results</h1>'
                '<p class="lead">The four main theorem families and every named auxiliary statement, with their precise scope and concrete compiled endpoints.</p>'
                '<p>Parts (a) and (b) of the unknown-spectrum and PCT theorems share one manuscript label. This index counts labels, not table rows or Lean declarations.</p>'
                '<label class="filter-label" for="result-filter">Filter results</label>'
                '<input id="result-filter" type="search" placeholder="Try LAN, projector, fidelity, or PBW…" autocomplete="off">'
                '<p id="result-count" class="small muted" aria-live="polite">27 results</p>'
                '<div class="cards results-grid">'
                + "".join(self.result_card(r, "../") for r in self.results.values()) + "</div>")
        self.page("results/index.html", "27 named results", body, "results")
        for result in self.results.values():
            body = (f'<div class="eyebrow">{esc(result["citation"])} · paper result</div><h1>{esc(result["title"])}</h1>'
                    f'<p>{self.paper_link(result["label"])} <span class="badge">Mapped to compiled Lean</span></p>'
                    '<section class="paper-correspondence"><h2>Paper statement and informal argument</h2>'
                    '<p><strong>Statement:</strong> ' + self.paper_link('section:' + result["section"]) + '</p>'
                    '<p><strong>Argument:</strong> ' + ' · '.join(self.paper_link('section:' + number) for number in result["argument_sections"]) + '</p>'
                    f'<p><a href="../correspondence.html#{slug(result["label"])}">This result in the paper-to-Lean table →</a></p></section>'
                    '<div class="notice">Scope notes below come from the manuscript-to-Lean map. Exact source excerpts are the formal reference.</div>')
            for part in result["parts"]:
                if len(result["parts"]) > 1:
                    body += "<h2>" + esc(part["label"].replace(result["label"], result["citation"])) + "</h2>"
                body += '<section class="callout info"><h2>Hypotheses and correspondence</h2>' + paragraphs(part["scope"]) + "</section>"
                body += '<h2>Concrete Lean endpoints</h2><p class="small muted">These are exact statement excerpts, with proof bodies omitted. Section variables, instances, namespaces, imports, and proof bodies are visible in the linked full module.</p>'
                body += "".join(self.declaration(d) for d in part["pointers"])
            chapters = [c for c in self.chapters if result["label"] in c.get("manuscript_labels", [])]
            if chapters:
                body += '<section class="callout"><h2>Read this part of the proof</h2>' + "".join(
                    f'<p><a href="../guides/{c["id"]}.html">{esc(c["title"])} →</a><br>'
                    f'<a class="small" href="../dependencies.html#stage-{c["id"]}">View this stage’s dependencies →</a></p>'
                    for c in chapters) + "</section>"
            body += ('<details class="manuscript-excerpt"><summary>Exact manuscript TeX statement</summary>'
                     '<p class="small muted">Exact source excerpt identifying this statement. Read the paper for the surrounding mathematical exposition and notation.</p>'
                     f'<p class="small muted">Repository identifier: <code>{esc(result["label"])}</code></p>'
                     f'<pre class="code-block"><code>{esc(result["tex"])}</code></pre>'
                     f'<a href="{ARXIV}">Read the paper on arXiv ↗</a></details>')
            body += '<p><a href="index.html">← All named results</a></p>'
            self.page(result["url"], result["title"], body, "results")
            self.search.append({"title": result["title"], "subtitle": result["citation"], "kind": result["kind"].title(),
                                "url": result["url"], "text": result["label"] + ' ' + " ".join(p["scope"] for p in result["parts"])})

    def render_dependencies(self):
        data = self.dependencies
        nodes, edges = data["nodes"], data["edges"]
        incoming = {n["id"]: [] for n in nodes}
        outgoing = {n["id"]: [] for n in nodes}
        for edge in edges:
            incoming[edge["to"]].append(edge)
            outgoing[edge["from"]].append(edge)
        # A deterministic layered drawing of the ingredient DAG. Comparisons do
        # not impose a logical dependency or change a stage's layer.
        depths = {}

        def depth(stage):
            if stage not in depths:
                parents = [e["from"] for e in incoming[stage] if e.get("kind", "ingredient") == "ingredient"]
                depths[stage] = 1 + max(depth(p) for p in parents) if parents else 0
            return depths[stage]

        isolated = [n for n in nodes if not incoming[n["id"]] and not outgoing[n["id"]]]
        layers = {}
        for node in nodes:
            if node not in isolated:
                layers.setdefault(depth(node["id"]), []).append(node)
        width, node_width, node_height, stride = 1100, 190, 70, 120
        offset = stride if isolated else 0
        positions = {}
        for layer, row in sorted(layers.items()):
            for i, node in enumerate(row):
                positions[node["id"]] = ((i + .5) * width / len(row), 20 + offset + layer * stride)
        for i, node in enumerate(isolated):
            positions[node["id"]] = ((i + .5) * width / len(isolated), 20)
        height = 20 + offset + max(layers, default=0) * stride + node_height + 30
        svg = (f'<svg class="dependency-graph" viewBox="0 0 {width} {height}" role="group" '
               'aria-labelledby="dependency-diagram-title dependency-diagram-desc">'
               '<title id="dependency-diagram-title">The mixed-state cloning proof stages</title>'
               '<desc id="dependency-diagram-desc">Solid arrows run from ingredients to the stages that use them. '
               'Dotted arrows show comparison benchmarks. Select a stage for its guide, results, and Lean evidence.</desc>'
               '<defs><marker id="dependency-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="5" markerHeight="5" orient="auto-start-reverse">'
               '<path d="M 0 0 L 10 5 L 0 10 z" fill="#175e58"/></marker>'
               '<marker id="dependency-comparison-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="5" markerHeight="5" orient="auto-start-reverse">'
               '<path d="M 0 0 L 10 5 L 0 10 z" fill="#a36820"/></marker></defs>')
        for i, edge in enumerate(edges):
            sx, sy = positions[edge["from"]]
            tx, ty = positions[edge["to"]]
            source_edges, target_edges = outgoing[edge["from"]], incoming[edge["to"]]
            sx += (source_edges.index(edge) - (len(source_edges) - 1) / 2) * 24
            tx += (target_edges.index(edge) - (len(target_edges) - 1) / 2) * 28
            sy += node_height
            kind = edge.get("kind", "ingredient")
            if ty - sy > stride:
                # Long edges run through the gaps beside the middle layer,
                # then turn below it rather than crossing a stage's card.
                turn = ty - 20 - (i % 3) * 4
                path = f"M {sx:g} {sy:g} V {turn:g} H {tx:g} V {ty:g}"
            else:
                mid = (sy + ty) / 2
                path = f"M {sx:g} {sy:g} C {sx:g} {mid:g}, {tx:g} {mid:g}, {tx:g} {ty:g}"
            marker = "dependency-comparison-arrow" if kind == "comparison" else "dependency-arrow"
            svg += (f'<path class="dependency-edge" data-from="{esc(edge["from"])}" data-to="{esc(edge["to"])}" '
                    f'data-kind="{kind}" d="{path}" marker-end="url(#{marker})">'
                    f'<title>{esc(self.dependency_nodes[edge["from"]]["label"])} → '
                    f'{esc(self.dependency_nodes[edge["to"]]["label"])}: {esc(edge["label"])}</title></path>')
        for i, node in enumerate(nodes, 1):
            stage = node["id"]
            x, y = positions[stage]
            description = "Definitions used throughout" if node in isolated else f"Proof stage {i:02}"
            svg += (f'<g class="dependency-node" data-stage="{esc(stage)}"><a href="#stage-{esc(stage)}" '
                    f'aria-label="Select {esc(node["label"])}">'
                    f'<rect x="{x - node_width / 2:g}" y="{y:g}" width="{node_width}" height="{node_height}"/>'
                    f'<text class="dependency-node-number" x="{x:g}" y="{y + 22:g}" text-anchor="middle">{esc(description)}</text>'
                    f'<text x="{x:g}" y="{y + 47:g}" text-anchor="middle">{esc(node["label"])}</text></a></g>')
        svg += "</svg>"
        body = (f'<div class="eyebrow">The proof at a glance</div><h1>{esc(data["title"])}</h1>'
                f'<p class="lead">{inline(data["intro"])}</p>'
                f'<div id="dependency-map" class="dependency-map" data-default-stage="{esc(data["default_stage"])}">'
                '<div class="dependency-legend"><span class="dependency-legend-item"><span class="dependency-legend-line"></span>Ingredient → stage that uses it</span>'
                '<span class="dependency-legend-item"><span class="dependency-legend-line" data-kind="comparison"></span>Comparison benchmark</span></div>'
                '<p class="dependency-pan-hint">Swipe the diagram sideways to explore all stages.</p>'
                '<div class="dependency-graph-wrap" tabindex="0" aria-label="Proof dependency diagram; scroll horizontally on a narrow screen">'
                + svg + '</div><div class="dependency-controls">'
                '<p class="small muted">Select a stage to highlight its direct ingredients and uses. Open its guide for the informal argument, or inspect the Lean evidence below.</p>'
                '<div class="dependency-selectors" role="group" aria-label="Select a proof stage">'
                + "".join(f'<button type="button" class="dependency-selector" data-stage="{esc(n["id"])}">{esc(n["label"])}</button>' for n in nodes)
                + '</div><button type="button" id="dependency-reset" class="dependency-reset">Show all stages</button>'
                f'<p id="dependency-status" class="dependency-status" role="status">All {len(nodes)} stages are shown. Each arrow is explained in the linked stage notes below.</p></div>')

        def edge_list(stage, relations, direction):
            if not relations:
                return ""
            result = f'<h3>{direction}</h3><ul>'
            for edge in relations:
                other = edge["from"] if edge["to"] == stage else edge["to"]
                kind = edge.get("kind", "ingredient")
                tag = ' <span class="badge">Comparison</span>' if kind == "comparison" else ""
                result += (f'<li><a href="#stage-{esc(other)}">{esc(self.dependency_nodes[other]["label"])}</a>'
                           f' — {inline(edge["label"])}{tag}<details class="dependency-evidence"><summary>Lean evidence</summary><ul>')
                for evidence in edge["evidence"]:
                    pointer = evidence["_pointer"]
                    result += (f'<li>{inline(evidence["note"])}<br><a href="{esc(pointer["url"])}">'
                               f'<code>{esc(pointer["name"])}</code></a> '
                               f'<span class="small muted">line {pointer["line"]}</span></li>')
                result += "</ul></details></li>"
            return result + "</ul>"

        public_nodes, public_edges = [], []
        for node in nodes:
            stage = node["id"]
            chapter = self.dependency_chapters[stage]
            labels = chapter.get("manuscript_labels", [])
            body += (f'<article class="dependency-detail" id="stage-{esc(stage)}" data-stage="{esc(stage)}">'
                     f'<h2>{esc(node["label"])}</h2><p>{inline(chapter["summary"])}</p>'
                     f'<a class="button secondary" href="guides/{esc(stage)}.html">Read the informal proof guide →</a>')
            if labels:
                body += '<h3>Named results</h3><ul>' + "".join(
                    f'<li><a href="{esc(self.results[label]["url"])}">{esc(self.results[label]["title"])}</a> '
                    f'<span class="badge">{esc(self.results[label]["citation"])}</span></li>' for label in labels) + "</ul>"
            body += '<details><summary>Where this stage appears in the paper</summary>' + self.paper_locations(chapter) + '</details>'
            body += edge_list(stage, incoming[stage], "Ingredients and benchmarks")
            body += edge_list(stage, outgoing[stage], "Where this stage contributes")
            endpoints = {p["name"]: p for step in chapter["steps"] for p in step["_pointers"]}
            endpoints.update({r["_pointer"]["name"]: r["_pointer"] for r in chapter["results"]})
            body += '<details><summary>Lean endpoints in this stage</summary><ul>' + "".join(
                f'<li><a href="{esc(p["url"])}"><code>{esc(p["name"])}</code></a></li>'
                for p in endpoints.values()) + "</ul></details></article>"
            public_nodes.append({**node, "guide_url": f"guides/{stage}.html", "results": [
                {k: self.results[label][k] for k in ("label", "title", "url")} for label in labels]})
            self.search.append({"title": "Dependency map: " + node["label"], "subtitle": chapter["title"],
                                "kind": "Map", "url": "dependencies.html#stage-" + stage,
                                "text": chapter["summary"] + " " + " ".join(e["label"] for e in incoming[stage] + outgoing[stage])})
        for edge in edges:
            public_edges.append({k: edge.get(k, "ingredient") for k in ("from", "to", "kind", "label")})
            public_edges[-1]["evidence"] = [{"note": e["note"], **{k: e["_pointer"][k] for k in ("name", "file", "line", "url")}} for e in edge["evidence"]]
        self.put("data/dependencies.json", json.dumps({"title": data["title"], "semantics": data["legend"],
                 "source_audit_sha256": self.latest["run_sha256"], "nodes": public_nodes, "edges": public_edges}, indent=2, ensure_ascii=False) + "\n")
        body += ('</div><section class="callout"><h2>Reading the arrows</h2>' + paragraphs(data["legend"])
                 + '<p>These stage connections are editorial. The builder checks each source pointer against the compiled audit; the arrow labels summarize the mathematical argument. '
                 'Qualitative estimates and concrete channel assemblies are identified separately from named generic auxiliary theorems in the evidence notes.</p>'
                 '<p>The physical problem supplies definitions throughout the proof. The exact all-density optimum remains open; degenerate-spectrum and fixed-rank formulas remain conjectures.</p>'
                 '<p><a href="scope.html">Open questions and conjectures →</a> · <a href="data/dependencies.json">Download the map data</a></p></section>')
        self.page("dependencies.html", "Proof dependency map", body, "dependencies",
                  extra_assets=("dependencies.css", "dependencies.js"))
        self.search.append({"title": "Dependency map", "subtitle": "Ingredients, results, and Lean evidence",
                            "kind": "Page", "url": "dependencies.html", "text": "proof dependencies roadmap graph " + data["intro"]})

    def render_sources(self):
        rows = []
        stage_modules = {}
        paper_modules = {}
        for result in self.results.values():
            for module in {p["module"] for part in result["parts"] for p in part["pointers"]}:
                paper_modules.setdefault(module, []).append(result)
        for chapter in self.chapters:
            pointers = [p for step in chapter["steps"] for p in step["_pointers"]]
            pointers += [r["_pointer"] for r in chapter["results"]]
            for module in {p["module"] for p in pointers}:
                stage_modules.setdefault(module, []).append(chapter)
        for edge in self.dependencies["edges"]:
            chapter = self.dependency_chapters[edge["to"]]
            for evidence in edge["evidence"]:
                chapters = stage_modules.setdefault(evidence["_pointer"]["module"], [])
                if chapter not in chapters:
                    chapters.append(chapter)
        for module, info in self.modules.items():
            source_lines = info["text"].splitlines()
            short = module.removeprefix("Cloning.")
            rows.append(f'<tr data-filter-text="{esc(module.lower())}"><td><a href="{module}.html"><code>{esc(short)}</code></a></td><td>{len(source_lines):,}</td><td>{len(info["declarations"])}</td></tr>')
            body = (f'<div class="eyebrow">Exact Lean source</div><h1 class="source-title">{esc(short)}</h1>'
                    f'<p><code>{esc(info["file"])}</code></p>'
                    f'<p class="small muted">Source hash: <code>{sha(info["text"])}</code></p>'
                    f'<div class="actions"><a class="button secondary" href="raw/{module}.lean">Download .lean</a>'
                    f'<a class="button secondary" href="{GITHUB}{esc(info["file"])}">View on GitHub ↗</a>'
                    '<a href="index.html">All modules</a></div>'
                    '<p class="small muted">Full source copied without mathematical changes from the snapshot whose input hash matches the passing audit. Select a line number for a stable source pointer.</p>')
            if module in stage_modules:
                body += '<p class="small">In the dependency map: ' + " · ".join(
                    f'<a href="../dependencies.html#stage-{c["id"]}">{esc(self.dependency_nodes[c["id"]]["label"])}</a>'
                    for c in stage_modules[module]) + "</p>"
            if module in paper_modules:
                body += '<details class="paper-correspondence"><summary>Paper ↔ Lean correspondence in this module</summary><ul>' + "".join(
                    f'<li>{self.paper_link(r["label"])} · <a href="../{r["url"]}">{esc(r["title"])}</a> · '
                    f'<a href="../correspondence.html#{slug(r["label"])}">Informal argument and formal endpoints</a></li>'
                    for r in paper_modules[module]) + '</ul></details>'
            if info["declarations"]:
                body += '<details><summary>Declarations in this module</summary><div class="module-declarations">'
                body += "".join(f'<a href="#L{d["line"]}"><span class="badge">{esc(d["kind"])}</span> <code>{esc(d["name"])}</code></a>' for d in info["declarations"])
                body += "</div></details>"
            body += '<div class="code-wrap source-wrap"><pre class="source-lines"><code>'
            body += "".join(
                f'<span class="source-line" id="L{i}"><a class="line-no" href="#L{i}" aria-label="Line {i}">{i}</a>'
                f'<span class="line-code">{esc(line) or " "}</span></span>\n'
                for i, line in enumerate(source_lines, 1))
            body += "</code></pre></div>"
            self.page(info["url"], short + " · Lean source", body, "source")
            self.put("source/raw/" + module + ".lean", info["text"])
            self.search.append({"title": module, "subtitle": f"Lean module · {len(source_lines)} lines",
                                "kind": "Module", "url": info["url"], "text": short})
            for d in info["declarations"]:
                self.search.append({"title": d["name"], "subtitle": module + f" · line {d['line']}",
                                    "kind": d["kind"].title(), "url": d["url"], "text": d["source_name"]})
        body = ('<div class="eyebrow">Browse the formalization</div><h1>Lean source modules</h1>'
                f'<p class="lead">{len(self.modules):,} complete modules, copied from the audited source snapshot. Every page works offline and every line has an anchor.</p>'
                '<p>The declaration index lists source declarations that can be matched unambiguously to the compiled audit inventory. Generated declarations are included in the full audit, but are not presented as handwritten source declarations.</p>'
                '<label class="filter-label" for="result-filter">Filter modules</label><input id="result-filter" type="search" placeholder="Search module names…" autocomplete="off">'
                f'<p id="result-count" class="small muted" aria-live="polite">{len(rows)} modules</p>'
                '<div class="table-wrap"><table><thead><tr><th>Module</th><th>Lines</th><th>Indexed declarations</th></tr></thead><tbody>'
                + "".join(rows) + "</tbody></table></div>")
        self.page("source/index.html", "Lean source modules", body, "source")

    def render_scope(self):
        scope = self.guides["scope"]
        body = ('<div class="eyebrow">Read claims precisely</div><h1>Scope and conventions</h1>'
                '<p class="lead">The formal proof has explicit hypotheses. These conventions keep the manuscript, the guide, and Lean aligned.</p>'
                '<h2>What is proved</h2>' + (items(scope["proved"]) if isinstance(scope["proved"], list) else paragraphs(scope["proved"])))
        body += '<section class="callout info"><h2>Fidelity convention</h2>' + paragraphs(scope["fidelity"]) + "</section>"
        conventions = []
        section = ""
        for line in self.map_text.splitlines():
            if line.startswith("## "):
                section = line[3:]
            if section != "Conventions and objects" or not line.startswith("|"):
                continue
            cells = [x.strip() for x in line.strip("|").split("|")]
            if len(cells) == 2 and cells[0] not in ("Manuscript object", "---"):
                conventions.append("<tr><th>" + inline(cells[0]) + "</th><td>" + inline(cells[1]) + "</td></tr>")
        body += '<h2>Object and parameter dictionary</h2><div class="table-wrap"><table><tbody>' + "".join(conventions) + "</tbody></table></div>"
        body += '<section class="callout"><h2>Open questions and unproved conjectures</h2>' + items(scope["open"]) + "</section>"
        body += ('<h2>How to read a source excerpt</h2><p>The displayed text is taken directly from a Lean file. Its type may use variables and instances declared earlier in the module. The full source link includes those declarations, the namespace, imports, and the complete proof.</p>'
                 '<p>English summaries and chapter groupings are editorial. They are checked for valid source pointers, but they are not themselves Lean propositions or a new axiom audit.</p>'
                 '<p><a href="reference/PROOF_MAP.md">Download the complete manuscript-to-Lean map</a> · <a href="verification.html">Verification record →</a></p>')
        self.page("scope.html", "Scope and conventions", body, "scope")
        self.search.append({"title": "Scope, conventions, and open questions", "subtitle": "What the formalization claims", "kind": "Page",
                            "url": "scope.html", "text": "root fidelity squared infidelity conjectures degenerate all-state optimum limits"})

    def render_verification(self):
        a, r = self.audit, self.run
        checker_rows, checker_statuses = [], {}
        for name, title in (("comparator", "Comparator"), ("nanoda", "Nanoda")):
            path = FORMAL / "verification" / name / "status.json"
            summary = self.read_json(path) if path.is_file() else {"status": "not_run"}
            record, binding, lock_sha256 = None, None, None
            if summary.get("run_record"):
                relative = PurePosixPath(summary["run_record"])
                archive = ROOT / relative
                archive_root = FORMAL / "verification" / name
                if relative.is_absolute() or not archive.resolve().is_relative_to(archive_root.resolve()):
                    raise ValueError(f"{name} run record must be archived under its verification directory")
                if sha(archive.read_bytes()) != summary.get("run_record_sha256"):
                    raise ValueError(f"{name} archived run record hash differs")
                record = self.read_json(archive)
                self.put(f"data/{name}-run.json", json.dumps(record, indent=2) + "\n")
                if summary.get("status") == "passed":
                    lock_sha256 = sha(self.read(FORMAL / "verification/tools-lock.json"))
                    if name == "nanoda":
                        binding = self.read_json(archive.parent / "binding.json")
                        self.put("data/nanoda-binding.json", json.dumps(binding, indent=2) + "\n")
            verdict = checker_verdict(name, summary, record, self.latest["run_sha256"],
                                      a["audited_constants"], lock_sha256, binding)
            checker_statuses[name] = {"recorded_status": summary.get("status", "not_run"),
                                      "displayed_verdict": verdict}
            self.put(f"data/{name}-status.json", json.dumps(summary, indent=2) + "\n")
            evidence = f'<a href="data/{name}-status.json">Status record</a>'
            if record is not None:
                evidence += f' · <a href="data/{name}-run.json">Archived run</a>'
            if name == "comparator" and summary.get("mode") == "trusted-local-no-sandbox":
                verdict += "; trusted local execution without a sandbox"
            checker_rows.append(f'<tr><th>{title}</th><td>{esc(verdict)}</td><td>{evidence}</td></tr>')
        rows = [
            ("Pinned Lean toolchain", self.lean_version),
            ("Recorded result", r["status"]),
            ("Audit completed (UTC)", r["completed_utc"]),
            ("Implementation modules", f'{a["modules"]:,}'),
            ("Source theorems", f'{a["theorems"]:,}'),
            ("Compiled constants audited", f'{a["audited_constants"]:,}'),
            ("Allowed logical axioms", ", ".join(a["allowed_axioms"])),
            ("Placeholder scan", a["source_placeholder_scan"]),
            ("Axiom audit", a["axiom_audit"]),
            ("Run manifest SHA-256", self.latest["run_sha256"]),
        ]
        body = ('<div class="eyebrow">Evidence and reproducibility</div><h1>Verification</h1>'
                '<p class="lead">The wiki is generated from a recorded passing Lean build and full declaration axiom audit. Its builder checks source hashes before displaying that evidence.</p>'
                '<div class="table-wrap"><table><tbody>' + "".join(f'<tr><th>{esc(k)}</th><td><code>{esc(v)}</code></td></tr>' for k, v in rows) + "</tbody></table></div>"
                '<h2>Three distinct checks</h2><ol>'
                '<li><strong>Lean build:</strong> the formal statements and proof terms elaborate under the pinned toolchain.</li>'
                '<li><strong>Axiom audit:</strong> every compiled declaration exported by the imported implementation modules is checked against the three standard logical axioms listed above.</li>'
                '<li><strong>Wiki integrity:</strong> manuscript labels, editorial pointers, source line anchors, local links, and deterministic generated files are checked by the site builder.</li></ol>'
                '<p>The site builder does not rerun the Lean build or the axiom audit. It verifies that its source files match the selected audit’s recorded hashes, and that referenced declarations occur in both source and compiled inventory.</p>'
                '<section class="callout"><h2>Independent checker status</h2>'
                '<div class="table-wrap"><table><tbody>' + "".join(checker_rows) + '</tbody></table></div>'
                '<p>These are recorded checker results, separate from the Lean build and axiom audit above. Preparation, readiness, failure, and incomplete execution provide no completed certificate. A displayed pass requires a hash-matched archived full-run record bound to this exact audit; the site builder does not execute either checker.</p></section>'
                '<h2>Rebuild or check this wiki</h2><p>From the repository root, using Python 3.10 or newer:</p>'
                '<pre class="code-block"><code>python3 tools/docs-site/build.py\npython3 tools/docs-site/build.py --check</code></pre>'
                '<p>Open <code>docs/index.html</code> directly in a browser, or serve the directory with any static web server. Search, mathematics, navigation, and source pages use bundled assets and relative URLs; no network request is needed.</p>'
                '<h2>Reproduce the formal audit</h2>'
                '<p>The repository’s verification runner and pinned Lean project remain the authoritative workflow. The commands below run from the repository root:</p>'
                '<pre class="code-block"><code>cd formalization\nlake build All\npython3 scripts/check_checkpoint.py\npython3 scripts/audit.py --jobs 3</code></pre>'
                '<p class="small">The checkpoint command checks saved evidence without running Lean. The audit command performs a fresh build and complete compiled-declaration audit. See the <a href="reference/VERIFICATION.md">complete verification instructions</a> for output directories and scope.</p>'
                '<h2>Inspect the evidence</h2><ul>'
                '<li><a href="data/audit-summary.json">Audit summary copied into this wiki</a></li>'
                '<li><a href="manifest.json">Wiki inputs, source pointers, and generated-file hashes</a></li>'
                f'<li><a href="{GITHUB}formalization/{self.latest["directory"]}/run.json">Complete recorded run manifest ↗</a></li>'
                f'<li><a href="{GITHUB}formalization/{self.latest["directory"]}/verification.json">Complete verification report ↗</a></li>'
                '<li><a href="README.md">Site build and maintenance notes</a></li></ul>'
                '<h2>Design and bundled software</h2>'
                '<p>The reading-route, named-result, and exact-source organization is inspired by the <a href="https://tianyipeng.github.io/fermats-last-theorem/">Fermat’s Last Theorem proof wiki</a> and its <a href="https://github.com/anthropics/fermats-last-theorem/tree/main/html">HTML project</a>. This site uses its own layout, styles, and generator.</p>'
                '<p>Mathematics is rendered locally by KaTeX using native MathML. KaTeX is distributed under the <a href="assets/vendor/katex/LICENSE">MIT license</a>; no third-party styles or fonts are loaded.</p>')
        self.page("verification.html", "Verification", body, "verification")
        self.put("data/audit-summary.json", json.dumps({
            "recorded_run": self.latest["directory"],
            "run_sha256": self.latest["run_sha256"],
            "status": r["status"], "completed_utc": r["completed_utc"],
            "toolchain": self.lean_version, "modules": a["modules"],
            "theorems": a["theorems"], "audited_constants": a["audited_constants"],
            "allowed_axioms": a["allowed_axioms"], "axiom_audit": a["axiom_audit"],
            "source_placeholder_scan": a["source_placeholder_scan"],
            "independent_checkers": checker_statuses,
            "note": "Copied evidence summary, not a new execution of Lean or the axiom audit."
        }, indent=2) + "\n")

    def render(self):
        self.render_overview()
        self.render_correspondence()
        self.render_guides()
        self.render_results()
        self.render_dependencies()
        self.render_sources()
        self.render_scope()
        self.render_verification()
        for path in sorted(ASSETS.rglob("*")):
            if path.is_file():
                self.put("assets/" + path.relative_to(ASSETS).as_posix(), path.read_bytes())
                self.inputs[path.relative_to(ROOT).as_posix()] = sha(path.read_bytes())
        for asset in ("assets/site.css", "assets/site.js", "assets/dependencies.css", "assets/dependencies.js",
                      "assets/vendor/katex/katex.min.js"):
            if asset not in self.files:
                raise ValueError("Missing required static asset " + asset)
        self.put("assets/search-index.js", "window.PROOF_SEARCH="
                 + json.dumps(self.search, ensure_ascii=False, separators=(",", ":")).replace("</", "<\\/")
                 + ";\n")
        # New pages must not reuse stale CSS, interactions, or search data from a prior build.
        for asset in ("assets/site.css", "assets/site.js", "assets/search-index.js",
                      "assets/dependencies.css", "assets/dependencies.js"):
            versioned = asset + "?v=" + sha(self.files[asset])[:12]
            for path in self.files:
                if path.endswith(".html"):
                    self.files[path] = self.files[path].replace(
                        (asset + '"').encode(), (versioned + '"').encode())
        self.put("reference/cloning.tex", (FORMAL / "reference/cloning.tex").read_bytes())
        self.put("reference/PROOF_MAP.md", offline_proof_map(self.map_text))
        self.put("reference/VERIFICATION.md", self.read(FORMAL / "scripts/README.md"))
        self.put(".nojekyll", "")
        self.put(GENERATED_MARKER, "Generated by tools/docs-site/build.py. Do not edit docs/ by hand.\n")
        self.put("README.md", self.readme())
        pointers = {p["name"]: p for p in self.pointer_uses}
        manifest = {
            "generator": "tools/docs-site/build.py",
            "generator_sha256": sha(Path(__file__).read_bytes()),
            "recorded_lean_audit": self.latest,
            "counts": {"named_results": len(self.results), "chapters": len(self.chapters),
                       "source_modules": len(self.modules), "indexed_declarations": len(self.declarations),
                       "dependency_stages": len(self.dependencies["nodes"]),
                       "dependency_edges": len(self.dependencies["edges"]),
                       "paper_sections": len(self.paper_sections),
                       "guides_with_paper_correspondence": len(self.chapters),
                       "guide_steps_with_paper_references": sum(len(c["steps"]) for c in self.chapters),
                       "validated_guide_and_map_declarations": len(pointers), "search_entries": len(self.search)},
            "inputs": dict(sorted(self.inputs.items())),
            "pointers": sorted(pointers.values(), key=lambda x: x["name"]),
            "outputs_sha256": {p: sha(v) for p, v in sorted(self.files.items())},
        }
        self.put("manifest.json", json.dumps(manifest, indent=2, ensure_ascii=False) + "\n")
        validate_links(self.files)
        return manifest

    def readme(self):
        return f"""# Cloning proof wiki

Open [index.html](index.html) in a browser. The complete generated site works
offline, including search, mathematical display, all 27 named manuscript
results, chapter guides, the [dependency map](dependencies.html), and the
{len(self.modules)} audited Lean module pages. The map connects twelve proof
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

The audit snapshot is {self.latest["directory"]}, completed
{self.run["completed_utc"]}. manifest.json records input hashes and all
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
"""


class LinkParser(HTMLParser):
    def __init__(self):
        super().__init__()
        self.ids, self.links = set(), []

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if "id" in attrs:
            if attrs["id"] in self.ids:
                raise ValueError("Duplicate HTML id " + attrs["id"])
            self.ids.add(attrs["id"])
        for attribute in ("href", "src"):
            if attribute in attrs:
                self.links.append(attrs[attribute])


def validate_links(files):
    pages = {}
    links = {}
    for path, content in files.items():
        if path.endswith(".html"):
            parser = LinkParser()
            try:
                parser.feed(content.decode())
            except ValueError as error:
                raise ValueError(f"{path}: {error}") from error
            pages[path] = parser
            links[path] = parser.links
        elif path.endswith(".md"):
            text = content.decode()
            links[path] = [match[1].strip("<>") for match in MARKDOWN_LINK.finditer(text)]
            links[path].extend(match[1] or match[2] for match in MARKDOWN_REFERENCE.finditer(text))
    for path, references in links.items():
        for href in references:
            url = urlsplit(href)
            if unquote(url.path).lower().endswith(".tex"):
                raise ValueError(f"Reader-facing TeX source link is not allowed: {path}: {href}")
            if url.scheme or url.netloc:
                continue
            raw = unquote(url.path)
            target = PurePosixPath(path).parent / raw if raw else PurePosixPath(path)
            parts = []
            for part in target.parts:
                if part == "..":
                    if not parts:
                        raise ValueError(f"Link leaves generated docs: {path}: {href}")
                    parts.pop()
                elif part != ".":
                    parts.append(part)
            resolved = "/".join(parts)
            if resolved not in files:
                raise ValueError(f"Broken local link: {path}: {href} -> {resolved}")
            if url.fragment and resolved in pages and unquote(url.fragment) not in pages[resolved].ids:
                raise ValueError(f"Broken local anchor: {path}: {href}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Validate inputs, links and exact generated output without writing")
    args = parser.parse_args()
    try:
        wiki = Wiki()
        manifest = wiki.render()
        if args.check:
            existing = {p.relative_to(OUT).as_posix(): p.read_bytes() for p in OUT.rglob("*") if p.is_file()}
            differences = sorted(p for p in set(existing) | set(wiki.files) if existing.get(p) != wiki.files.get(p))
            if differences:
                raise ValueError("Generated site is stale or has extra files: " + ", ".join(differences[:12])
                                 + (f" (+{len(differences) - 12} more)" if len(differences) > 12 else ""))
        else:
            if OUT.exists() and any(OUT.iterdir()) and not (OUT / GENERATED_MARKER).exists():
                raise ValueError("Refusing to replace a nonempty docs/ without the generator marker")
            OUT.mkdir(exist_ok=True)
            for path in sorted(OUT.rglob("*"), reverse=True):
                if path.is_file() and path.relative_to(OUT).as_posix() not in wiki.files:
                    path.unlink()
                elif path.is_dir() and not any(path.iterdir()):
                    path.rmdir()
            for path, content in wiki.files.items():
                destination = OUT / path
                destination.parent.mkdir(parents=True, exist_ok=True)
                if not destination.exists() or destination.read_bytes() != content:
                    destination.write_bytes(content)
        counts = manifest["counts"]
        print(("PASS: generated wiki is current" if args.check else "Built docs/index.html")
              + f"; {counts['named_results']} named results; {counts['chapters']} chapters; "
              + f"{counts['source_modules']} source modules; "
              + f"{counts['validated_guide_and_map_declarations']} unique verified proof pointers; "
              + f"{len(wiki.files)} files. All local links and anchors passed.")
    except (ValueError, KeyError, FileNotFoundError, json.JSONDecodeError) as error:
        print("ERROR: " + str(error), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
