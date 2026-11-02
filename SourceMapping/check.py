#!/usr/bin/env python3
"""Check release documentation identity and correspondence inventories, not mathematics.

No network access, Lean execution, pin refresh, or writes. Default mode requires a
manifest sealed against a final fold. --allow-draft is for private fixtures only.

The main page (main-theorem.md) documents the release statement
NearQuarticWires.Release.ReleaseStatement against the joint paper (paper/paper.tex): its blocks are
re-rendered from the statement files and the paper and compared byte for byte, and every declaration of the closure
of the joint statement must be printed on it (mainmap.py). Its paper labels are those of the joint paper.
"""
import argparse
import hashlib
import html
import json
import re
import sys
import unicodedata
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import mainmap  # noqa: E402

SCHEMA = "near-cubic-gates/source-map/2"
PAPER_SHA = "acabd90c76bdabdcccafe7e598b92f46089115a28603a97799c13c372a94d7aa"
# Canonical JSON of all eight reviewed source entries, including exact PDF/text
# pins and release-relative paths. Removing sources must not turn INCOMPLETE into COMPLETE.
SOURCE_CATALOG_SHA = "e438953bc2f2631f24dc4c5868fda702d8b89134da042dba49aa48c3055ce92a"
PREFIX = "NearCubicGates.Published."
# Published statements kept in Statement.lean as transcription records, not assumed by the release.
RECORDED_NOT_ASSUMED = {PREFIX + "BCGT13.BCGT13_Theorem11_1"}
# Namespaces of published statements that the release no longer contains.
REMOVED_NAMESPACES = {"Apostol"}
LEAVES = {
    PREFIX + x for x in (
        "Williams.RectangularProductLeaf",
        "BCGT13.BCGT13_Theorem11_1_Fixed", "Shoup.FindIrrPolyAlgorithm17",
        "STV.Theorem29", "CW19Proximity.Lemma22Half", "CW19Code.Lemma26")
}
# Exact consumer producers and dependencies. Order is not mathematically relevant.
EXPECTED = {
    "normalization": ("Normalization.IntegerThreshold", "Normalization.threshold_normalization", ()),
    "restriction": ("Restriction.CentralBinomial", "Restriction.centralBinomialRestriction", ()),
    "bernstein": ("Probability.BernsteinFinite", "Probability.finiteBernstein", ()),
    "rectangularProduct": ("Williams.Final", "Williams.Final.williams14_of_leaf", ("Williams.RectangularProductLeaf",)),
    "shortPCP": ("Assembly.Field6Fixed", "Assembly.Fixed.field6OrdinaryFixed", ("BCGT13.BCGT13_Theorem11_1_Fixed", "Shoup.FindIrrPolyAlgorithm17")),
    "refuter": ("Assembly.Field7", "Assembly.field7", ()),
    "amplification": ("Amplification.Field8", "Amplification.field8", ("STV.Theorem29",)),
    "threeQueryPCPP": ("Assembly.Field9Encoder", "Assembly.field9Encoder", ("CW19Proximity.Lemma22Half", "CW19Code.Lemma26")),
}
EXPECTED_TYPES = {
    "normalization": "NearCubicWires.Bindings.CTW26.CTW26_Lemma3_2",
    "restriction": "NearCubicGates.PublishedSources.Witness.CTW26_AppendixA3_CentralBinomialRestriction",
    "bernstein": "NearCubicGates.PublishedSources.Witness.Vershynin18_Theorem2_8_4_FiniteBernstein.{0, 0}",
    "rectangularProduct": "NearCubicWires.Bindings.Williams14.Williams14_Corollary4_4",
    "shortPCP": "NearCubicGates.Adapters.Assembly.OrdinaryOracleCircuitPCP",
    "refuter": "NearCubicWires.Bindings.CLW20Theorem113.CLW20_Theorem1_13",
    "amplification": "NearCubicGates.Close.CLW20_Lemma3_9_Multitape",
    "threeQueryPCPP": "NearCubicGates.PublishedSources.PCPP.PerfectThreeQueryProximityLiteral ∧ NearCubicGates.Adapters.Assembly.EfficientLinearEncoder",
}
PAGES = ["README.md", "paper/README.md", "SourceMapping/README.md", "SourceMapping/main-theorem.md",
         "SourceMapping/tomography.md", "SourceMapping/masks.md"] + [
    "SourceMapping/" + x for x in (
        "1-threshold-normalization.md", "2-live-restriction.md", "3-bernstein.md",
        "5-rectangular-product.md", "6-short-pcp.md",
        "7-refuter.md", "8-amplification.md", "9-three-query-pcpp.md")]
CORE = {"Statement.lean", "NineInputs.lean", "SourceAdapters/Assembly.lean",
        "Check.lean", "Challenge.lean", "Solution.lean", "paper/near-cubic-gates-v3.tex", "CITATION.cff",
        "SourceMapping/check.py", "SourceMapping/mainmap.py", "SourceMapping/generate.py",
        "SourceMapping/source-tables.json", "scripts/fetch_sources.sh",
        "paper/paper.tex", "paper/published-inputs.tex", "StatementSupport.lean",
        "Proof/Quartic/Statement/Final.lean", "Proof/Quartic/Statement/Joint.lean",
        "Proof/Quartic/Statement/Release.lean", "comparator.json", "paper/paper.pdf", "paper/fig-cell.tex", "paper/joint-statement-verbatim.txt",
        "paper/proof-dag.tex", "paper/app-attribution.tex", "paper/app-lean-map.tex", "paper/app-statements.tex",
        "paper/app-earlier.tex"}
# Pages whose paper labels are those of the joint paper.
JOINT_PAGES = {"SourceMapping/main-theorem.md", "README.md", "paper/README.md", "SourceMapping/tomography.md",
               "SourceMapping/masks.md"}
MAIN_PAGE = "SourceMapping/main-theorem.md"
JOINT_PAPER = "paper/paper.tex"
JOINT_PAPER_SHA = "32c365c3c97134031d57cc7fe42432513408376fadb04ada31f3a9205b38070e"
# Input pages 2, 3 and 7 retain the version-3 statements with links to the gate companion. Their exact bytes
# are pinned below. Pages 1, 5, 6, 8 and 9 differ: page 1
# counts six retained statements, page 6 documents the input at the tuple (2, 4, 0, 1), and pages 5, 6, 8 and 9 print
# their published statements in Lean (generated). The version-3 page 4 (the prime number theorem) is not in the release.
V3_INPUT_PAGES = {
    "SourceMapping/2-live-restriction.md": "8003485f35dd277a934ce972f6359f3b226b5e1d89c0b319ee2fc494d1a0aa1a",
    "SourceMapping/3-bernstein.md": "513ee755c9bc9b0122b3745d6e99d610e5e48c722128a916953ba1317027e498",
    "SourceMapping/7-refuter.md": "c4ce8f23ebed33f84f7ac27fcecc5359fee215434f5175d4e68a8bd34906b4ff",
}
LABEL = re.compile(r"`((?:lem|imp|thm|def|app|rem|sec):[^`]+)`")
LINK = re.compile(r"\[[^\]]*\]\(([^)\s]+)\)")


class CheckError(Exception):
    pass


def need(condition, message):
    if not condition:
        raise CheckError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def within(root, name):
    p = (root / name).resolve()
    need(p.is_relative_to(root.resolve()), f"path outside release: {name}")
    return p


def unique(items, label):
    need(len(items) == len(set(items)), f"duplicate {label}")


def inventory(leaves, fields):
    unique(leaves, "leaf")
    need(set(leaves) == LEAVES, "trusted leaf inventory differs from the exact six leaves")
    names = [r["field"] for r in fields]
    unique(names, "derived field")
    need(set(names) == set(EXPECTED), "derived field inventory differs from the exact eight fields")
    for row in fields:
        mod, decl, deps = EXPECTED[row["field"]]
        need(row["module"] == "SourceAdapters." + mod, f"producer module: {row['field']}")
        need(row["decl"] == "NearCubicGates.Adapters." + decl, f"producer declaration: {row['field']}")
        unique(row["leaves"], "producer dependency")
        need(set(row["leaves"]) == {PREFIX + s for s in deps}, f"producer dependencies: {row['field']}")
        need(row.get("joins") == [], f"open producer joins: {row['field']}")
        need(row.get("type") == EXPECTED_TYPES[row["field"]], f"canonical producer conclusion type: {row['field']}")


def links(root, pages):
    files, count = set(), 0
    for name in pages:
        text = within(root, name).read_text()
        for target in LINK.findall(text):
            if target.startswith(("https://", "http://", "mailto:")):
                continue
            rel, _, frag = target.partition("#")
            p = within(root, str(Path(name).parent / rel)) if rel else within(root, name)
            need(p.exists(), f"missing local link: {name}: {target}")
            if p.is_file():
                files.add(str(p.relative_to(root.resolve())))
            if frag:
                # Current pages deliberately use file links and named labels in prose.
                m = re.fullmatch(r"L([0-9]+)(?:-L([0-9]+))?", frag)
                need(m is not None and p.is_file(), f"unsupported local anchor: {name}: {target}")
                lo, hi = int(m[1]), int(m[2] or m[1])
                need(1 <= lo <= hi <= len(p.read_text().splitlines()), f"line anchor: {name}: {target}")
            count += 1
    return files, count


def normalize(text):
    text = unicodedata.normalize("NFKC", html.unescape(text))
    for a, b in (("−", "-"), ("–", "-"), ("’", "'"), ("“", '"'), ("”", '"')):
        text = text.replace(a, b)
    return re.sub(r"\s+", "", text)


def source_checks(root, sources, quotes, pages):
    ids = [s["id"] for s in sources]
    unique(ids, "source id")
    catalog = {s["id"]: s for s in sources}
    present, absent = [], []
    for s in sources:
        p = within(root, s["file"])
        if not p.is_file():
            absent.append(s["id"])
        else:
            need(sha(p.read_bytes()) == s["sha256"], f"source PDF identity: {s['id']}")
            present.append(s["id"])
    verified, transcription, unchecked = [], [], []
    for i, q in enumerate(quotes):
        need(q["source"] in catalog, f"unknown quoted source: {i}")
        need(q["page"] in pages, f"unlisted quote page: {i}")
        need(q["text"] in html.unescape(within(root, q["page"]).read_text()), f"quote not printed: {i}")
        need(sha(q["text"].encode()) == q["sha256"], f"quote identity: {i}")
        s = catalog[q["source"]]
        need(q.get("pdf_sha256") == s["sha256"], f"quote/source PDF identity mismatch: {i}")
        first, last = q.get("pdf_page"), q.get("pdf_page_end", q.get("pdf_page"))
        need(type(first) is int and type(last) is int and 1 <= first <= last <= first + 1,
             f"quote PDF page span: {i}")
        if q.get("transcribed", False):
            transcription.append(i)
            continue
        if q["source"] not in present or not s.get("text"):
            unchecked.append(i)
            continue
        p = within(root, s["text"])
        if not p.is_file():
            unchecked.append(i)
            continue
        need(sha(p.read_bytes()) == s["text_sha256"], f"source text identity: {s['id']}")
        body = p.read_text()
        # pdftotext form feeds delimit physical PDF pages. No whole-document fallback.
        chunks = body.split("\f")
        need(last <= len(chunks), f"quote PDF page: {i}")
        need(normalize(q["text"]) in normalize("".join(chunks[first - 1:last])),
             f"quote absent from pinned page span: {i}")
        verified.append(i)
    return {"source_files_verified": present, "source_files_unavailable": absent,
            "quote_indices_verified": verified, "quote_indices_transcribed_not_verified": transcription,
            "quote_indices_unchecked": unchecked,
            "source_quote_status": "COMPLETE" if not absent and not unchecked and not transcription else "INCOMPLETE"}


def render_lint_text(name, text):
    """Check raw-HTML boundaries outside literal pre and fenced-code contents."""
    lines = text.splitlines()
    table_depth = 0
    in_pre = False
    fence = None
    raw_html = False
    previous_comment_safe = False
    pre_count = link_count = 0
    block_tag = re.compile(r"^ {0,3}</?(?:table|thead|tbody|tfoot|tr|td|th|p|div|h[1-6]|ul|ol|li|blockquote)(?:[ />])", re.I)
    for i, line in enumerate(lines):
        stripped = line.strip()
        where = f"{name}:{i + 1}"
        if in_pre:
            if "</pre>" in line.lower():
                in_pre = False
                raw_html = False
            continue
        if fence:
            if re.fullmatch(r" {0,3}" + re.escape(fence[0]) + "{" + str(len(fence)) + r",}\s*", line):
                fence = None
            continue
        if not stripped:
            raw_html = False
            previous_comment_safe = False
            continue
        fenced = re.match(r"^ {0,3}(`{3,}|~{3,})(.*)$", line)
        if fenced and not raw_html:
            fence = fenced[1]
            previous_comment_safe = False
            continue
        # Inline code is literal, not an opening raw-HTML pre element.
        visible = re.sub(r"(`+).*?\1", "", line)
        if re.search(r"<pre\b", visible, re.I):
            need(re.fullmatch(r" {0,3}<pre(?:\s+[^>]*)?>\s*", line, re.I) is not None,
                 f"render lint: malformed or inline pre opening: {where}")
            need(i > 0 and not lines[i - 1].strip(), f"render lint: pre lacks preceding blank line: {where}")
            pre_count += 1
            in_pre = True
            raw_html = False
            previous_comment_safe = False
            continue
        whole_comment = re.fullmatch(r"\s*<!--.*?-->\s*", line) is not None
        if whole_comment:
            # A comment after td without a blank is still inside the type-6 HTML block.
            previous_comment_safe = not raw_html and (i == 0 or not lines[i - 1].strip() or previous_comment_safe)
            continue
        if table_depth and LINK.search(visible):
            need(not raw_html and (i > 0 and (not lines[i - 1].strip() or previous_comment_safe)),
                 f"render lint: table link lacks safe blank/comment boundary: {where}")
            link_count += 1
        previous_comment_safe = False
        table_depth += len(re.findall(r"<table(?:\s[^>]*)?>", visible, re.I))
        table_depth -= len(re.findall(r"</table\s*>", visible, re.I))
        need(table_depth >= 0, f"render lint: unmatched table close: {where}")
        if block_tag.match(line):
            raw_html = True
    need(fence is None, f"render lint: unclosed fenced code: {name}")
    need(not in_pre, f"render lint: unclosed pre: {name}")
    need(not table_depth, f"render lint: unclosed table: {name}")
    return {"pre_blocks": pre_count, "table_link_lines": link_count}


def render_lint(root):
    pages = sorted((root / "SourceMapping").glob("*.md"))
    totals = {"render_lint_pages": len(pages), "render_lint_pre_blocks": 0, "render_lint_table_link_lines": 0}
    for path in pages:
        name = str(path.relative_to(root))
        row = render_lint_text(name, within(root, name).read_text())
        totals["render_lint_pre_blocks"] += row["pre_blocks"]
        totals["render_lint_table_link_lines"] += row["table_link_lines"]
    return totals


def check(root, manifest, allow_draft=False):
    root = root.resolve()
    m = json.loads(manifest.read_text())
    need(m["schema"] == SCHEMA, "unsupported manifest schema")
    final = m["status"] == "final-sealed"
    need(final or allow_draft, "manifest is not final-sealed")
    need(m["status"] in ("final-sealed", "private-fixture"), "invalid manifest status")
    inventory(m["trusted_leaves"], m["derived_fields"])
    catalog_bytes = json.dumps(m["published_sources"], sort_keys=True, ensure_ascii=False,
                               separators=(",", ":")).encode()
    need(sha(catalog_bytes) == SOURCE_CATALOG_SHA, "reviewed source catalog differs (IDs, PDF/text pins or paths)")
    fetch_text = within(root, "scripts/fetch_sources.sh").read_text()
    fetch_pins = re.findall(r'^CATALOG_SHA = "([0-9a-f]{64})"$', fetch_text, flags=re.M)
    need(fetch_pins == [SOURCE_CATALOG_SHA], "source-fetch helper and reviewed source catalog differ")
    need(set(m["pages"]) == set(PAGES) and len(m["pages"]) == len(PAGES), "page inventory")
    pins = m["pins"]
    need(str(manifest.resolve().relative_to(root)) not in pins, "manifest must not pin itself")
    required = CORE | set(PAGES) | {r["module"].replace(".", "/") + ".lean" for r in m["derived_fields"]}
    need(required <= set(pins), f"missing required pins: {sorted(required - set(pins))}")
    for name, digest in pins.items():
        p = within(root, name)
        need(p.is_file() and re.fullmatch("[0-9a-f]{64}", digest), f"missing/invalid pinned artifact: {name}")
        need(sha(p.read_bytes()) == digest, f"changed pinned artifact: {name}")
    need(pins["paper/near-cubic-gates-v3.tex"] == PAPER_SHA, "the gate companion's paper is not its version-3 source")
    for name, digest in V3_INPUT_PAGES.items():
        need(pins.get(name) == digest, f"input page differs from the version-3 release: {name}")
    provenance = m["provenance"]
    if final:
        need(provenance["fold_mode"] == "final", "not a final fold")
        need(provenance["open_fields"] == [], "fold has open fields")
        need(provenance["statement_sha256"] == pins["Statement.lean"], "stale final Statement pin")
        need(provenance["obligations_sha256"] == provenance["canonical_obligations_sha256"], "stale canonical obligations")
        need(provenance["registry_sha256"] == provenance["read_registry_sha256"], "stale fold registry")
    statement = within(root, "Statement.lean").read_text()
    found = re.search(r"structure PublishedInputs : Prop where\n(.*?)(?=\n(?:/--|def FinalStatement))", statement, re.S)
    need(found is not None, "PublishedInputs declaration missing")
    actual = re.findall(r"^\s+\w+\s*:\s*(NearCubicGates\.Published\.[\w.]+)\s*$", found[1], re.M)
    rows = [line.strip() for line in found[1].splitlines() if line.strip()]
    need(len(rows) == len(actual) == len(LEAVES) and set(actual) == LEAVES, "actual PublishedInputs differs from manifest")
    need(re.search(r"def FinalStatement\s*:\s*Prop\s*:=\s*PublishedInputs\s*→\s*NearCubicGates.Target.MainStatement", statement), "final implication declaration missing")
    for r in m["derived_fields"]:
        p = within(root, r["module"].replace(".", "/") + ".lean")
        short = r["decl"].split(".")[-1]
        need(re.search(r"^theorem\s+" + re.escape(short) + r"\b", p.read_text(), re.M), f"producer theorem absent: {r['decl']}")
    rendering = render_lint(root)
    linked, nlinks = links(root, PAGES)
    need(linked <= set(pins), f"linked files lack pins: {sorted(linked - set(pins))}")
    paper = within(root, "paper/near-cubic-gates-v3.tex").read_text()
    need(pins[JOINT_PAPER] == JOINT_PAPER_SHA, "joint paper is not the sealed version")
    joint = within(root, JOINT_PAPER).read_text()

    def cited(p):
        text = within(root, p).read_text()
        if p == MAIN_PAGE or p in mainmap.INPUT_PAGES or p in mainmap.RESULT_PAGES:  # quotations are verbatim sources, not citations
            text = re.sub(r"<pre[^>]*>.*?</pre>", "", text, flags=re.S)
        return sorted(set(LABEL.findall(text)))

    actual_labels = {p: cited(p) for p in PAGES}
    need(m["paper_labels"] == actual_labels, "paper label inventory differs from pages")
    labels = set(re.findall(r"\\label\{([^}]+)\}", paper))
    joint_labels = set(re.findall(r"\\label\{([^}]+)\}", joint))
    for page, names in actual_labels.items():
        have = joint_labels if page in JOINT_PAGES else labels
        need(set(names) <= have, f"missing paper label: {page}: {set(names) - have}")
    for page in ("README.md", "paper/README.md", "SourceMapping/README.md"):
        text = within(root, page).read_text()
        stray = set(re.findall(r"\b[0-9a-f]{64}\b", text)) - set(pins.values())
        need(not stray, f"a SHA-256 in {page} is not the digest of a pinned file: {sorted(stray)}")
    # No page names a published statement other than the six fields of PublishedInputs (outside verbatim quotations).
    namespaces = set(re.findall(r"^namespace NearCubicGates\.Published\.(\w+)", statement, re.M)) | REMOVED_NAMESPACES
    short = re.compile(r"`(?:NearCubicGates\.Published\.)?((?:" + "|".join(sorted(namespaces)) + r")\.[A-Za-z0-9_]+)`"
                       r"|NearCubicGates\.Published\.(\w+\.[A-Za-z0-9_]+)")
    for page in PAGES:
        prose = re.sub(r"<pre[^>]*>.*?</pre>", "", within(root, page).read_text(), flags=re.S)
        # Only selectors in the pages re-rendered by mainmap are metadata, not prose premises.
        # Unrecognized comments remain subject to the published-premise inventory check.
        if page == MAIN_PAGE or page in mainmap.INPUT_PAGES or page in mainmap.RESULT_PAGES:
            prose = re.sub(r"<!-- (?:lean [\w.']+|paper [^\n<>]+|files|closure|statement|"
                           r"source-table [A-Za-z0-9_.:-]+|/(?:lean|paper|files|closure|statement|source-table)) -->",
                           "", prose)
        for name in (x or y for x, y in short.findall(prose)):
            need(PREFIX + name in LEAVES or PREFIX + name in RECORDED_NOT_ASSUMED,
                 f"{page} names a published statement that is not a field of PublishedInputs: {name}")
    printed_main, main_result = mainmap.verify(m)
    input_result = mainmap.verify_inputs(m, printed_main)
    result_pages = mainmap.verify_results(m)
    source = source_checks(root, m["published_sources"], m["quotes"], PAGES)
    return {"status": "IDENTITY_PASS" if final else "PRIVATE_FIXTURE_PASS_NOT_RELEASE",
            "scope": "Documentation identity/inventory/links only; no mathematical or kernel certification.",
            "trusted_leaves": len(LEAVES), "derived_fields": len(EXPECTED), "pinned_artifacts": len(pins),
            "pages": len(PAGES), "local_links": nlinks, "paper_labels": sum(map(len, actual_labels.values())),
            **main_result, **input_result, **result_pages, **source, **rendering}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    ap.add_argument("--manifest", type=Path)
    ap.add_argument("--allow-draft", action="store_true")
    args = ap.parse_args()
    try:
        print(json.dumps(check(args.root, args.manifest or args.root / "SourceMapping/manifest.json", args.allow_draft), indent=2))
    except (CheckError, mainmap.CheckError, KeyError, ValueError, OSError, TypeError) as e:
        print(f"FAIL {e}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
