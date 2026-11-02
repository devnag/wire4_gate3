#!/usr/bin/env python3
"""The main page of this source mapping: blocks that quote the statement files and the paper verbatim.

`generate.py` writes the blocks of main-theorem.md from the current files; `check.py` re-renders them and compares
byte for byte. A block is one of:

    <!-- lean NAME -->        the declaration NAME, verbatim from its doc comment to its last line, with a link
    <!-- paper file=F label=L -->                  the LaTeX environment that carries \\label{L} in F, verbatim
    <!-- paper file=F from="TEXT" to="TEXT" -->    the lines of F from the line containing one text to the next line
                                                   containing the other, verbatim
    <!-- files -->, <!-- closure -->               the files quoted, with SHA-256, and the closure count

The closure of the main statement (the declarations of the statement files that it uses) is computed by Lean
(`generate.py --closure`) and recorded in manifest.json; every declaration of it must be printed on the page.
"""
import hashlib
import html
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
PAGE = "SourceMapping/main-theorem.md"
STATEMENT_FILES = ["Statement.lean", "StatementSupport.lean", "Proof/Quartic/Statement/Final.lean",
                   "Proof/Quartic/Statement/Joint.lean", "Proof/Quartic/Statement/Release.lean"]
MAIN_ROOT = "NearQuarticWires.Statement.JointStatement4"
# The input pages that print the published statements, with the statements (types of the fields of `PublishedInputs`)
# whose closures they print. A declaration is printed once: on the main page, or on the first input page whose
# statements reach it.
# Pages for results of independent interest: paper statements beside Lean declarations of these files.
RESULT_PAGES = {
    "SourceMapping/tomography.md": ["Proof/Quartic/Tomography.lean", "Proof/Quartic/Reusable.lean",
                                    "Proof/Gates/ScalarWindow.lean", "Proof/Gates/TomographyDirections.lean"],
    "SourceMapping/masks.md": ["Proof/Quartic/Mask/Polynomial.lean", "Proof/Quartic/Reusable.lean"],
}
INPUT_PAGES = {
    "SourceMapping/5-rectangular-product.md": ["NearCubicGates.Published.Williams.RectangularProductLeaf"],
    "SourceMapping/6-short-pcp.md": ["NearCubicGates.Published.BCGT13.BCGT13_Theorem11_1_Fixed",
                                     "NearCubicGates.Published.Shoup.FindIrrPolyAlgorithm17"],
    "SourceMapping/8-amplification.md": ["NearCubicGates.Published.STV.Theorem29"],
    "SourceMapping/9-three-query-pcpp.md": ["NearCubicGates.Published.CW19Proximity.Lemma22Half",
                                          "NearCubicGates.Published.CW19Code.Lemma26"],
}
RELEASE = "NearQuarticWires.Release.ReleaseStatement"
FORBIDDEN = re.compile(r"\b(?:" + "|".join(["so" + "rry(?:Ax)?", "adm" + "it", "native" + "_decide", "ext" + "ern",
                                 "implemented" + "_by", "un" + "safe"]) + r")\b", re.I)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def esc(text):
    return html.escape(text, quote=False)


def inside(path):
    return path.resolve().is_relative_to(ROOT.resolve())


def read_lines(rel):
    path = ROOT / rel
    if not path.is_file() or not inside(path):
        fail(f"missing file: {rel}")
    return file_text(rel).splitlines()


class CheckError(Exception):
    pass


def fail(msg):
    raise CheckError(msg)


# ---------------------------------------------------------------------------------------------------------------
# Lean declarations, read from the source text. A declaration runs from its doc comment (or attributes) to the
# last non-blank line before the next command that starts in column 0; this equals the range Lean records.

DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|private|protected|partial|nonrec)\s+)*"
                  r"(def|theorem|lemma|abbrev|structure|class|inductive|instance|opaque)\s+([^\s(:{\[]+)")
CONTINUATION = ("deriving", "|", "termination_by", "decreasing_by", "where", ")", "}")


def lean_decls(lines):
    """Map each declaration's full name to (first line, last line, declaring line), 1-based."""
    out, scopes, starts = {}, [], []
    for i, line in enumerate(lines):
        m = re.match(r"^namespace\s+(\S+)", line)
        if m:
            scopes.append(m.group(1))
            continue
        if re.match(r"^section\b", line):
            scopes.append(None)
            continue
        if re.match(r"^end\b", line):
            if scopes:
                scopes.pop()
            continue
        m = DECL.match(line)
        if m:
            name = m.group(2)
            prefix = ".".join(s for s in scopes if s)
            if name.startswith("_root_."):
                full = name[len("_root_."):]
            else:
                full = f"{prefix}.{name}" if prefix else name
            starts.append((i, full))
    for i, full in starts:
        first, j = i, i - 1
        while j >= 0:
            if lines[j].startswith("@["):
                first, j = j, j - 1
                continue
            if lines[j].rstrip().endswith("-/"):
                k = j
                while k >= 0 and not lines[k].lstrip().startswith("/-"):
                    k -= 1
                if k >= 0 and lines[k].lstrip().startswith("/--"):
                    first = k
            break
        last, k = i, i + 1
        while k < len(lines):
            s = lines[k]
            if s and not s[0].isspace() and not s.startswith(CONTINUATION):
                break
            if s.strip():
                last = k
            k += 1
        out[full] = None if full in out else (first + 1, last + 1, i + 1)
    return {k: v for k, v in out.items() if v is not None}


_DECL_CACHE, _TEXT_CACHE = {}, {}


def file_text(rel):
    if rel not in _TEXT_CACHE:
        _TEXT_CACHE[rel] = (ROOT / rel).read_text(encoding="utf-8")
    return _TEXT_CACHE[rel]



def decls_of(rel):
    if rel not in _DECL_CACHE:
        _DECL_CACHE[rel] = lean_decls(read_lines(rel))
    return _DECL_CACHE[rel]


def find_decl(name, files):
    """The unique file among `files` that declares `name`, with its range."""
    short = name.rsplit(".", 1)[-1]
    hits = []
    for rel in files:
        if short not in file_text(rel):
            continue
        d = decls_of(rel)
        if name in d:
            hits.append((rel, *d[name]))
        elif "." not in name:
            hits += [(rel, *v) for full, v in d.items() if full.rsplit(".", 1)[-1] == name]
    if len(hits) != 1:
        fail(f"declaration `{name}` is declared {len(hits)} times in {', '.join(files) if len(files) < 6 else 'the repository'}")
    return hits[0]


# ---------------------------------------------------------------------------------------------------------------
# Paper excerpts

def tex_env(lines, label):
    """The lines of the environment that carries \\label{label}: from its \\begin (on the label's line or at most
    two lines above it) to the matching \\end."""
    tag = "\\label{" + label + "}"
    at = [i for i, line in enumerate(lines) if tag in line]
    if len(at) != 1:
        fail(f"label {label} occurs {len(at)} times")
    i = at[0]
    for b in range(i, max(i - 3, -1), -1):
        envs = re.findall(r"\\begin\{([^}]+)\}", lines[b])
        if not envs:
            continue
        env = envs[-1]
        level = 0
        for e in range(b, len(lines)):
            level += lines[e].count("\\begin{" + env + "}") - lines[e].count("\\end{" + env + "}")
            if level <= 0:
                if e >= i:
                    return b + 1, e + 1
                break
    fail(f"no environment begins at label {label}")


def tex_span(lines, start_text, end_text, max_lines=200):
    at = [i for i, line in enumerate(lines) if start_text in line]
    if len(at) != 1:
        fail(f"paper span start {start_text!r} occurs {len(at)} times")
    if type(max_lines) is not int or not 1 <= max_lines <= 200:
        fail("paper span limit must be between 1 and 200 lines")
    ends = [e for e in range(at[0], min(len(lines), at[0] + max_lines)) if end_text in lines[e]]
    if len(ends) != 1:
        fail(f"paper span end {end_text!r} occurs {len(ends)} times within {max_lines} lines after {start_text!r}")
    return at[0] + 1, ends[0] + 1


# ---------------------------------------------------------------------------------------------------------------
# Rendering of generated blocks. generate.py writes these blocks; this file re-renders them and compares.

BLOCK = re.compile(r"<!-- (lean|paper|files|closure|statement|source-table) ?(.*?) -->\n(.*?)<!-- /\1 -->", re.S)


def lines_label(start, end):
    return f"line {start}" if start == end else f"lines {start}–{end}"


def anchor(start, end):
    return f"#L{start}" if start == end else f"#L{start}-L{end}"


def parse_args(arg):
    out = {}
    for m in re.finditer(r'(\w+)=(?:"((?:[^"\\]|\\.)*)"|(\S+))', arg):
        out[m.group(1)] = (m.group(2).replace('\\"', '"') if m.group(2) is not None else m.group(3))
    return out


def lean_block(name, prefix="../", files=None):
    rel, first, last, _ = find_decl(name, files or STATEMENT_FILES)
    body = "\n".join(read_lines(rel)[first - 1:last]) + "\n"
    text = (f"[{rel}, {lines_label(first, last)}]({prefix}{rel}{anchor(first, last)})\n\n"
            f"<pre title=\"{rel}, {lines_label(first, last)}\">\n{esc(body)}</pre>\n")
    return text, {"kind": "lean", "declaration": name, "source": rel, "start": first, "end": last,
                  "sha256": sha(body.encode())}


def paper_block(arg, prefix="../"):
    a = parse_args(arg)
    rel = a["file"]
    lines = read_lines(rel)
    if "label" in a:
        first, last = tex_env(lines, a["label"])
    else:
        try:
            limit = int(a.get("max_lines", "200"))
        except ValueError:
            fail("paper span max_lines must be a positive integer")
        first, last = tex_span(lines, a["from"], a["to"], limit)
    body = "\n".join(lines[first - 1:last]) + "\n"
    text = (f"<b>{rel}, {lines_label(first, last)}</b> ([{rel}]({prefix}{rel}{anchor(first, last)}))\n\n"
            f"<pre>\n{esc(body)}</pre>\n")
    return text, {"kind": "paper", "source": rel, "start": first, "end": last, "sha256": sha(body.encode()),
                  "selector": {k: v for k, v in a.items() if k != "file"}}


def files_text(used, shas):
    lines = ["**Files.** The line numbers below are of these files:", ""]
    lines += [f"- [`{rel}`](../{rel}), SHA-256 `{shas[rel]}`" for rel in used]
    return "\n".join(lines) + "\n"


def closure_text(c):
    n, m = len(c["declarations"]), len(c["auxiliary"])
    return (f"The Lean column prints every declaration that `{MAIN_ROOT}` uses: all {n} declarations of its closure "
            f"in the statement files, each exactly as it appears there. The closure stops at Lean's core library and "
            f"Mathlib, whose definitions are not printed. Its {m} other constants are the constructors, fields and "
            f"recursors of the printed structures and inductive types, and constants that Lean generates while "
            f"elaborating the printed declarations.\n")


def used_files(text, statement_decls=(), files=None):
    files = files or STATEMENT_FILES
    used = []
    for m in BLOCK.finditer(text):
        if m.group(1) == "paper":
            rels = [parse_args(m.group(2))["file"]]
        elif m.group(1) == "lean":
            rels = [find_decl(m.group(2), files)[0]]
        elif m.group(1) == "statement":
            rels = [find_decl(d, STATEMENT_FILES)[0] for d in statement_decls]
        elif m.group(1) == "source-table":
            rels = ["Statement.lean", SOURCE_TABLES_FILE]
        else:
            continue
        for rel in rels:
            if rel not in used:
                used.append(rel)
    return used


def render(text, closure, statement_decls=(), files=None):
    """The page with every block regenerated from the current files; the excerpt records; the files used."""
    used = used_files(text, statement_decls, files)
    shas = {rel: sha((ROOT / rel).read_bytes()) for rel in used}
    recs = []

    def block(m):
        kind, arg = m.group(1), m.group(2)
        if kind == "lean":
            body, rec = lean_block(arg, files=files)
            recs.append(rec)
        elif kind == "paper":
            body, rec = paper_block(arg)
            recs.append(rec)
        elif kind == "source-table":
            body, rec = source_table_block(arg)
            recs.append(rec)
        elif kind == "statement":
            parts = []
            for d in statement_decls:
                b, rec = lean_block(d)
                parts.append(b)
                recs.append(rec)
            body = "\n".join(parts)
        elif kind == "files":
            body = files_text(used, shas)
        else:
            body = closure_text(closure)
        return f"<!-- {kind}{(' ' + arg) if arg else ''} -->\n{body}<!-- /{kind} -->"

    return BLOCK.sub(block, text), recs, shas


def verify(manifest):
    """Re-render the main page and compare; check the recorded excerpts and that the closure is printed."""
    mm = manifest["main_map"]
    text = (ROOT / PAGE).read_text(encoding="utf-8")
    if FORBIDDEN.search(text):
        fail("forbidden proof token on the main page")
    want, recs, shas = render(text, mm["closure"])
    if want != text:
        fail("stale block on the main page (run python3 SourceMapping/generate.py)")
    if recs != mm["excerpts"]:
        fail("manifest.json main_map excerpts differ from the page (run python3 SourceMapping/generate.py)")
    if shas != mm["files"]:
        fail("manifest.json main_map files differ from the page (run python3 SourceMapping/generate.py)")
    prose = re.sub(r"<pre[^>]*>.*?</pre>", "", text, flags=re.S)
    stray = sorted(set(re.findall(r"\b[0-9a-f]{64}\b", prose)) - set(shas.values()))
    if stray:
        fail(f"SHA-256 on the main page that is not the digest of a quoted file: {stray}")
    printed = {r["declaration"] for r in recs if r["kind"] == "lean"}
    missing = [d for d in mm["closure"]["declarations"] if d not in printed]
    if missing:
        fail(f"closure declarations not printed on the main page: {missing}")
    for aux, owner in mm["closure"]["auxiliary"].items():
        generated = any(part.startswith(("_", "match_", "proof_")) for part in aux.split("."))
        if not generated and not (owner in printed and aux.startswith(owner + ".")):
            fail(f"closure constant {aux} belongs to no printed declaration")
    if RELEASE not in printed:
        fail(f"the release statement {RELEASE} is not printed")
    return printed, {"main_page_lean_excerpts": sum(r["kind"] == "lean" for r in recs),
            "main_page_paper_excerpts": sum(r["kind"] == "paper" for r in recs),
            "main_closure_declarations_printed": len(mm["closure"]["declarations"]),
            "main_closure_auxiliary": len(mm["closure"]["auxiliary"])}


def decl_order(names):
    """Declarations in the order of the statement files (file, then line)."""
    def key(n):
        rel, first, _, _ = find_decl(n, STATEMENT_FILES)
        return (STATEMENT_FILES.index(rel), first)
    return sorted(names, key=key)


def assign_input_pages(release_closure, leaf_closures, printed_main):
    """For each input page, the declarations of its statements' closures not printed earlier (main page first)."""
    done, out = set(printed_main), {}
    for page, leaves in INPUT_PAGES.items():
        want = set()
        for leaf in leaves:
            want |= set(leaf_closures[leaf]["declarations"])
        out[page] = decl_order(sorted(want - done))
        done |= want
    missing = sorted(set(release_closure["declarations"]) - done)
    if missing:
        fail(f"release-closure declarations on no page: {missing}")
    return out


def verify_inputs(manifest, printed_main):
    """Re-render the input pages' statement blocks; every declaration of the closure of the release statement is
    printed on the main page or on an input page."""
    mm = manifest["main_map"]
    printed, n = set(printed_main), 0
    for page in INPUT_PAGES:
        text = (ROOT / page).read_text(encoding="utf-8")
        decls = mm["input_pages"][page]
        want, recs, shas = render(text, mm["closure"], decls)
        if want != text:
            fail(f"stale statement block on {page} (run python3 SourceMapping/generate.py)")
        if recs != mm["input_excerpts"][page]:
            fail(f"manifest.json input excerpts differ from {page}")
        expected_tables = [t["id"] for t in load_source_tables()["tables"] if t["page"] == page]
        if [r["table"] for r in recs if r["kind"] == "source-table"] != expected_tables:
            fail(f"published-source comparison tables are missing or reordered on {page}")
        printed |= {r["declaration"] for r in recs if r["kind"] == "lean"}
        n += sum(r["kind"] == "lean" for r in recs)
    rc = mm["release_closure"]
    missing = [d for d in rc["declarations"] if d not in printed]
    if missing:
        fail(f"closure declarations of the release statement printed on no page: {missing}")
    for aux, owner in rc["auxiliary"].items():
        generated = any(part.startswith(("_", "match_", "proof_")) for part in aux.split("."))
        if not generated and not (owner in printed and aux.startswith(owner + ".")):
            fail(f"release-closure constant {aux} belongs to no printed declaration")
    tables = load_source_tables()["tables"]
    if manifest["quotes"] != source_quotes_for_manifest():
        fail("manifest source quotes differ from the source-table data")
    return {"input_page_lean_excerpts": n, "release_closure_declarations_printed": len(rc["declarations"]),
            "release_closure_auxiliary": len(rc["auxiliary"]), "published_source_tables": len(tables),
            "published_source_rows": sum(len(t["rows"]) for t in tables),
            "published_source_quotes": sum(len(r["quotes"]) for t in tables for r in t["rows"])}


def verify_results(manifest):
    """Re-render the pages of the results of independent interest and compare."""
    mm = manifest["main_map"]
    n = 0
    for page, files in RESULT_PAGES.items():
        text = (ROOT / page).read_text(encoding="utf-8")
        if FORBIDDEN.search(text):
            fail(f"forbidden proof token on {page}")
        want, recs, shas = render(text, mm["closure"], files=files)
        if want != text:
            fail(f"stale block on {page} (run python3 SourceMapping/generate.py)")
        if recs != mm["result_excerpts"][page] or shas != mm["result_files"][page]:
            fail(f"manifest.json result excerpts differ from {page}")
        n += len(recs)
    return {"result_page_excerpts": n}


# Published-source tables repeat selected declarations; the complete release closure remains checked above.
SOURCE_TABLES_FILE = "SourceMapping/source-tables.json"
SOURCE_TABLE_SCHEMA = "near-cubic-gates/source-tables/1"
SOURCE_TABLES = {
    "williams": ("SourceMapping/5-rectangular-product.md", "NearCubicGates.Published.Williams.RectangularProductLeaf", "williams_rectangularProductLeaf", {"wilacc14-jacm"}),
    "bcgt-fixed": ("SourceMapping/6-short-pcp.md", "NearCubicGates.Published.BCGT13.BCGT13_Theorem11_1_Fixed", "bcgt13_theorem11_1", {"bcgt13-eccc-TR12-045-rev3"}),
    "shoup": ("SourceMapping/6-short-pcp.md", "NearCubicGates.Published.Shoup.FindIrrPolyAlgorithm17", "shoup_findIrrPolyAlgorithm17", {"bcgt13-eccc-TR12-045-rev3", "sho88-tr763"}),
    "stv": ("SourceMapping/8-amplification.md", "NearCubicGates.Published.STV.Theorem29", "stv_theorem29", {"stv01-eccc-rev2", "stv-journ"}),
    "cw-proximity": ("SourceMapping/9-three-query-pcpp.md", "NearCubicGates.Published.CW19Proximity.Lemma22Half", "cw19Proximity_lemma22Half", {"cw19-dagstuhl", "bghsv06-full"}),
    "cw-code": ("SourceMapping/9-three-query-pcpp.md", "NearCubicGates.Published.CW19Code.Lemma26", "cw19Code_lemma26", {"cw19-dagstuhl", "bghsv06-full"}),
}


def load_source_tables():
    data = json.loads((ROOT / SOURCE_TABLES_FILE).read_text(encoding="utf-8"))
    if set(data) != {"schema", "tables"} or data["schema"] != SOURCE_TABLE_SCHEMA:
        fail("unsupported published-source table schema")
    if not isinstance(data["tables"], list) or [t.get("id") for t in data["tables"]] != list(SOURCE_TABLES):
        fail("the six published-source tables are missing, duplicated or reordered")
    rows, quotes = set(), set()
    for t in data["tables"]:
        page, leaf, _, sources = SOURCE_TABLES[t["id"]]
        if t.get("page") != page or t.get("premises") != [leaf] or not t.get("title"):
            fail(f"source-table premise/page mismatch: {t['id']}")
        if not isinstance(t.get("notes"), list) or not all(isinstance(x, str) for x in t["notes"]):
            fail(f"invalid source-table notes: {t['id']}")
        if not t.get("rows") or leaf not in t["rows"][0].get("lean", []):
            fail(f"source-table first row does not print its premise: {t['id']}")
        for r in t["rows"]:
            rid = r.get("id", "")
            if not re.fullmatch(r"[A-Za-z0-9_.:-]+", rid) or rid in rows or not r.get("label"):
                fail("invalid or duplicate source-table row")
            rows.add(rid)
            if not r.get("lean") or not all(isinstance(n, str) for n in r["lean"]):
                fail(f"missing source-table Lean declarations: {rid}")
            for name in r["lean"]:
                find_decl(name, ["Statement.lean"])
            if not r.get("quotes"):
                fail(f"source-table row has no source quotation: {rid}")
            for q in r["quotes"]:
                qid = q.get("id", "")
                if not re.fullmatch(r"[A-Za-z0-9_.:-]+", qid) or qid in quotes:
                    fail("invalid or duplicate source quotation id")
                quotes.add(qid)
                if q.get("source") not in sources or not re.fullmatch(r"[0-9a-f]{64}", q.get("pdf_sha256", "")):
                    fail(f"source quotation has the wrong publication: {qid}")
                if not isinstance(q.get("text"), str) or not q["text"] or sha(q["text"].encode()) != q.get("sha256"):
                    fail(f"source quotation text/hash differs: {qid}")
                if any(ord(c) < 32 and c not in "\n\r\t" for c in q["text"]):
                    fail(f"source quotation contains an unprintable extraction glyph: {qid}")
                start, end = q.get("pdf_page"), q.get("pdf_page_end", q.get("pdf_page"))
                if type(start) is not int or type(end) is not int or not 1 <= start <= end <= start + 1:
                    fail(f"invalid bounded source quotation page span: {qid}")
                if not all(isinstance(q.get(k), str) and q[k] for k in ("printed_page", "locator", "revision")):
                    fail(f"source quotation locator missing: {qid}")
                if type(q.get("transcribed")) is not bool or (q["transcribed"] and not q.get("transcription_note")):
                    fail(f"source quotation transcription status missing: {qid}")
                if not isinstance(q.get("omissions"), list) or not all(isinstance(s, str) and s for s in q["omissions"]):
                    fail(f"source quotation omissions are not explicit: {qid}")
    return data


def source_quotes_for_manifest():
    out = []
    for t in load_source_tables()["tables"]:
        for row in t["rows"]:
            for q in row["quotes"]:
                out.append({**q, "page": t["page"], "table": t["id"], "row": row["id"]})
    return out


def published_field_block(field, expected_leaf):
    rel, first, last, _ = find_decl("NearCubicGates.Close.PublishedInputs", ["Statement.lean"])
    lines = read_lines(rel)
    hits = [i for i in range(first - 1, last) if lines[i].startswith("  " + field + " :")]
    if len(hits) != 1:
        fail(f"published premise field {field} is not unique")
    start, end = hits[0], hits[0] + 1
    while end < last and lines[end].startswith("    "):
        end += 1
    body = "\n".join(lines[start:end]) + "\n"
    rhs = " ".join(body.split(":", 1)[1].split())
    if rhs not in {expected_leaf, expected_leaf.removeprefix("NearCubicGates.")}:
        fail(f"published premise field {field} has type {rhs!r}, expected {expected_leaf}")
    name = "NearCubicGates.Close.PublishedInputs." + field
    text = (f'<p>Retained premise field <code>{esc(name)}</code>: '
            f'<a href="../{rel}{anchor(start + 1, end)}">{rel}, {lines_label(start + 1, end)}</a></p>\n'
            f'\n<pre>\n{esc(body)}</pre>\n')
    return text, {"kind": "lean-field", "declaration": name, "source": rel, "start": start + 1,
                  "end": end, "sha256": sha(body.encode())}


def source_table_block(table_id):
    data = load_source_tables()
    found = [t for t in data["tables"] if t["id"] == table_id]
    if len(found) != 1:
        fail(f"unknown source table: {table_id}")
    table = found[0]
    _, expected_leaf, field, _ = SOURCE_TABLES[table_id]
    out = ["<h3>" + esc(table["title"]) + "</h3>\n"]
    out += ["<p>" + esc(n) + "</p>\n" for n in table["notes"]]
    out += ['<table>\n<tr><th>Published source (verbatim)</th><th>Lean (verbatim)</th></tr>\n']
    records = []
    for index, row in enumerate(table["rows"]):
        out += ["<tr><td>\n", f"<p><b>{esc(row['label'])}</b></p>\n"]
        qrecs, lrecs = [], []
        for q in row["quotes"]:
            pages = str(q["pdf_page"]) + ("–" + str(q["pdf_page_end"]) if q.get("pdf_page_end") else "")
            out += [f"<p>{esc(q['revision'])}; {esc(q['locator'])}; printed p. {esc(q['printed_page'])}; "
                    f"PDF p. {pages}. Pinned PDF SHA-256 <code>{q['pdf_sha256']}</code>.</p>\n"]
            if q["transcribed"]:
                out += ["<p><i>" + esc(q["transcription_note"]) + "</i></p>\n"]
            if q["omissions"]:
                out += ["<p><b>Marked omissions:</b> " + esc("; ".join(q["omissions"])) + "</p>\n"]
            out += ["\n<pre>\n" + esc(q["text"]) + "\n</pre>\n"]
            qrecs.append({"id": q["id"], "sha256": q["sha256"], "source": q["source"],
                          "pdf_sha256": q["pdf_sha256"], "pdf_page": q["pdf_page"],
                          "pdf_page_end": q.get("pdf_page_end", q["pdf_page"])})
        out += ["</td><td>\n"]
        if index == 0:
            text, rec = published_field_block(field, expected_leaf)
            out.append(text)
            lrecs.append(rec)
        for name in row["lean"]:
            text, rec = lean_block(name, files=["Statement.lean"])
            out += [f"\n<!-- lean {name} -->\n" + text + "<!-- /lean -->\n"]
            lrecs.append(rec)
        if row.get("note"):
            out += ["<p>" + esc(row["note"]) + "</p>\n"]
        out += ["</td></tr>\n"]
        records.append({"row": row["id"], "quotes": qrecs, "lean": lrecs})
    out.append("</table>\n")
    return "".join(out), {"kind": "source-table", "table": table_id, "data_sha256": sha((ROOT / SOURCE_TABLES_FILE).read_bytes()),
                           "rows": records}
