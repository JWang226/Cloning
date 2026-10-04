"""Numbered locations in the frozen paper; no TeX compilation or web requests."""
import re


def paper_structure(text):
    """Read section and shared theorem counters, including remarks and appendices.

    The manuscript's amsthm/aliascnt declarations share one counter per
    section. A remark therefore consumes a number even though it is not one
    of the 27 named formalization targets. Starred headings consume neither.
    ArXiv v1 fragments are checked separately against saved heading metadata.
    """
    events = re.compile(
        r"\\appendix\b|\\(?P<heading>section|subsection|subsubsection)(?P<star>\*)?"
        r"\{(?P<title>[^{}]+)\}|\\begin\{(?P<kind>theorem|lemma|proposition|corollary|remark)\}")
    label_re = re.compile(r"\s*\\label(?:\[[^]]+\])?\{([^}]+)\}")
    sections, results = [], {}
    appendix, section, subsection, subsubsection, counter = False, 0, 0, 0, 0
    current, root_anchor, section_number = None, "", ""
    for event in events.finditer(text):
        if event[0] == r"\appendix":
            appendix, section, subsection, subsubsection, counter = True, 0, 0, 0, 0
            current = None
            continue
        if event["heading"]:
            if event["star"]:
                continue
            level = ("section", "subsection", "subsubsection").index(event["heading"])
            if level == 0:
                section += 1
                subsection = subsubsection = counter = 0
                section_number = chr(64 + section) if appendix else str(section)
                root_anchor = ("A" if appendix else "S") + str(section)
                number, anchor = section_number, root_anchor
            elif level == 1:
                subsection += 1
                subsubsection = 0
                number = f"{section_number}.{subsection}"
                anchor = f"{root_anchor}.SS{subsection}"
            else:
                subsubsection += 1
                number = f"{section_number}.{subsection}.{subsubsection}"
                anchor = f"{root_anchor}.SS{subsection}.SSS{subsubsection}"
            label = label_re.match(text, event.end())
            current = {"number": number, "title": event["title"].replace("--", "–"),
                       "anchor": anchor, "label": label[1] if label else "section:" + number}
            sections.append(current)
        else:
            if current is None:
                raise ValueError("Numbered paper result is outside a section")
            counter += 1
            end = text.find(r"\end{" + event["kind"] + "}", event.end())
            if end < 0:
                raise ValueError("Unclosed numbered paper environment")
            for label in re.findall(r"\\label\{((?:thm|lem|prop|cor):[^}]+)\}", text[event.end():end]):
                results[label] = {"number": f"{section_number}.{counter}",
                                  "citation": event["kind"].title() + f" {section_number}.{counter}",
                                  "anchor": f"{root_anchor}.Thmtheorem{counter}",
                                  "section": current["number"]}
    return sections, results


# Arguments appearing elsewhere than the statement. The remaining auxiliary
# results have their proof/derivation in the section containing the statement.
RESULT_ARGUMENTS = {
    "thm:known-optimum": ["2.1", "2.3", "3.3"],
    "thm:unknown-optimum": ["2.1", "2.2", "2.3", "3.3"],
    "thm:grassmann": ["4.1", "4.2", "4.3"],
    "thm:pct-comparison": ["5", "D.1", "D.2", "D.3"],
    "prop:sector-fidelity": ["A.1", "A.2"],
    "prop:young-rounding": ["B"],
    "thm:gaussian-amplification": ["3.1", "C.1", "C.2", "C.3"],
}
