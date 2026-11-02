#!/usr/bin/env python3
"""Regenerate the verbatim blocks of main-theorem.md and their records in manifest.json.

Run from the release root:

    python3 SourceMapping/generate.py             # blocks, excerpt records and pins from the current files
    python3 SourceMapping/generate.py --closure   # first recompute the closure of the joint statement with Lean
    python3 SourceMapping/generate.py --drop-absent   # in a pruned tree: unpin files that are not in it

The page is written by hand except for its marked blocks (see mainmap.py). The input pages are not touched. The
script also refreshes the pins of manifest.json for the main page, the files it quotes or links, the README and the
three scripts, and the inventory of paper labels cited by the main page outside its quotations.
"""
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import mainmap  # noqa: E402

ROOT = mainmap.ROOT

CLOSURE_QUERY = r"""
import Proof.Quartic.Statement.Release
open Lean

def libRoots : List Name :=
  [`Mathlib, `Init, `Std, `Lean, `Batteries, `Aesop, `Qq, `Plausible, `ImportGraph, `LeanSearchClient,
   `ProofWidgets, `Lake]

def inRepo (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => !(libRoots.contains (env.header.moduleNames[idx.toNat]!).getRoot)
  | none => false

def statementRefs (ci : ConstantInfo) : Array Name :=
  match ci with
  | .defnInfo d => ci.type.getUsedConstants ++ d.value.getUsedConstants
  | .opaqueInfo d => ci.type.getUsedConstants ++ d.value.getUsedConstants
  | .inductInfo d => ci.type.getUsedConstants ++ d.ctors.toArray
  | .ctorInfo d => ci.type.getUsedConstants.push d.induct
  | .recInfo d => ci.type.getUsedConstants ++ d.all.toArray
  | _ => ci.type.getUsedConstants

partial def statementClosure (env : Environment) (root : Name) : Array Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut stack := #[root]
  while h : stack.size > 0 do
    let n := stack.back
    stack := stack.pop
    if seen.contains n || !inRepo env n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      for m in statementRefs ci do
        if !seen.contains m then stack := stack.push m
  return seen.toArray.qsort (fun a b => a.toString < b.toString)

run_meta do
  let env ← getEnv
  for root in [ROOTS] do
    for n in statementClosure env root do
      IO.println s!"{root}\t{n}\t{n.isInternalDetail}"
"""


def closure():
    """The closures of the joint statement, the release statement and each published statement."""
    roots = [mainmap.MAIN_ROOT, mainmap.RELEASE] + [leaf for leaves in mainmap.INPUT_PAGES.values() for leaf in leaves]
    query = CLOSURE_QUERY.replace("[ROOTS]", "[" + ", ".join("`" + r for r in roots) + "]")
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "Closure.lean"
        path.write_text(query, encoding="utf-8")
        result = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT, capture_output=True, text=True)
    if result.returncode != 0:
        sys.exit(f"the Lean closure query failed:\n{result.stdout}\n{result.stderr}")
    table = {}
    for f in mainmap.STATEMENT_FILES:
        table.update(mainmap.decls_of(f))
    out = {r: {"declarations": [], "auxiliary": {}} for r in roots}
    for line in result.stdout.splitlines():
        parts = line.split("\t")
        if len(parts) != 3 or parts[0] not in out:
            continue
        root, name, internal = parts[0], parts[1], parts[2] == "true"
        decls, aux = out[root]["declarations"], out[root]["auxiliary"]
        if name in table:
            decls.append(name)
            continue
        segs = name.split(".")
        owner = next((".".join(segs[:k]) for k in range(len(segs) - 1, 0, -1) if ".".join(segs[:k]) in table), None)
        if owner is None and not internal:
            sys.exit(f"closure constant {name} is not declared in the statement files")
        aux[name] = owner
    return {r: {"declarations": sorted(v["declarations"]), "auxiliary": dict(sorted(v["auxiliary"].items()))}
            for r, v in out.items()}


LABEL = re.compile(r"`((?:lem|imp|thm|def|app|rem|sec):[^`]+)`")


def main_labels(text):
    outside = re.sub(r"<pre[^>]*>.*?</pre>", "", text, flags=re.S)
    return sorted(set(LABEL.findall(outside)))


def main():
    path = HERE / "manifest.json"
    manifest = json.loads(path.read_text(encoding="utf-8"))
    mm = manifest.setdefault("main_map", {})
    mm["paper"] = "paper/paper.tex"
    mm["root"] = mainmap.MAIN_ROOT
    mm["release"] = mainmap.RELEASE
    mm["statement_files"] = mainmap.STATEMENT_FILES
    if "--closure" in sys.argv:
        cl = closure()
        mm["closure"] = cl[mainmap.MAIN_ROOT]
        mm["release_closure"] = cl[mainmap.RELEASE]
        mm["leaf_closures"] = {leaf: cl[leaf] for leaves in mainmap.INPUT_PAGES.values() for leaf in leaves}
    if "closure" not in mm:
        sys.exit("no closure recorded: run with --closure")
    page = ROOT / mainmap.PAGE
    text, recs, shas = mainmap.render(page.read_text(encoding="utf-8"), mm["closure"])
    page.write_text(text, encoding="utf-8")
    mm["excerpts"] = recs
    mm["files"] = shas
    # the input pages: the closures of the published statements, each declaration printed once
    printed_main = {r["declaration"] for r in recs if r["kind"] == "lean"}
    mm["input_pages"] = mainmap.assign_input_pages(mm["release_closure"], mm["leaf_closures"], printed_main)
    mm["input_excerpts"] = {}
    for ipage, decls in mm["input_pages"].items():
        itext, irecs, _ = mainmap.render((ROOT / ipage).read_text(encoding="utf-8"), mm["closure"], decls)
        (ROOT / ipage).write_text(itext, encoding="utf-8")
        mm["input_excerpts"][ipage] = irecs
        manifest["paper_labels"][ipage] = main_labels(itext)
    mm["result_excerpts"], mm["result_files"] = {}, {}
    for rpage, rfiles in mainmap.RESULT_PAGES.items():
        rtext, rrecs, rshas = mainmap.render((ROOT / rpage).read_text(encoding="utf-8"), mm["closure"], files=rfiles)
        (ROOT / rpage).write_text(rtext, encoding="utf-8")
        mm["result_excerpts"][rpage], mm["result_files"][rpage] = rrecs, rshas
        manifest["paper_labels"][rpage] = main_labels(rtext)
    # pins: the main page, everything it quotes or links, the README and the scripts
    pins = manifest["pins"]
    linked = set()
    for target in re.findall(r"\[[^\]]*\]\(([^)\s]+)\)", re.sub(r"<pre[^>]*>.*?</pre>", "", text, flags=re.S)):
        if target.startswith(("http://", "https://")):
            continue
        rel = target.partition("#")[0]
        if rel:
            linked.add(str((page.parent / rel).resolve().relative_to(ROOT.resolve())))
    for rel in sorted(set(shas) | linked | set(mainmap.INPUT_PAGES) | set(mainmap.RESULT_PAGES) | {mainmap.PAGE, "SourceMapping/README.md", "SourceMapping/check.py",
                                            "SourceMapping/mainmap.py", "SourceMapping/generate.py"}):
        pins[rel] = mainmap.sha((ROOT / rel).read_bytes())
    # the release files and the release pages, with the files they link; the input pages are not touched
    import check as chk
    pages = ["README.md", "paper/README.md", "SourceMapping/README.md"]
    for page in chk.PAGES:  # every file a page links to is pinned
        ptext = re.sub(r"<pre[^>]*>.*?</pre>", "", (ROOT / page).read_text(encoding="utf-8"), flags=re.S)
        for target in re.findall(r"\[[^\]]*\]\(([^)\s]+)\)", ptext):
            rel = target.partition("#")[0]
            if not rel or target.startswith(("http://", "https://", "mailto:")):
                continue
            linked_path = ((ROOT / page).parent / rel).resolve()
            if linked_path.is_file():
                pins[str(linked_path.relative_to(ROOT.resolve()))] = mainmap.sha(linked_path.read_bytes())
    for rel in sorted(chk.CORE) + pages:
        if (ROOT / rel).is_file() and rel not in chk.V3_INPUT_PAGES:
            pins[rel] = mainmap.sha((ROOT / rel).read_bytes())
    for page in pages:
        ptext = (ROOT / page).read_text(encoding="utf-8")
        for target in re.findall(r"\[[^\]]*\]\(([^)\s]+)\)", ptext):
            if target.startswith(("http://", "https://", "mailto:")):
                continue
            rel = target.partition("#")[0]
            if not rel:
                continue
            linked_path = ((ROOT / page).parent / rel).resolve()
            if linked_path.is_file():
                pins[str(linked_path.relative_to(ROOT.resolve()))] = mainmap.sha(linked_path.read_bytes())
        manifest["paper_labels"][page] = sorted(set(LABEL.findall(ptext)))
    if "--drop-absent" in sys.argv:  # a pruned tree: files outside it are no longer pinned
        pins = {rel: d for rel, d in pins.items() if (ROOT / rel).is_file()}
    manifest["quotes"] = mainmap.source_quotes_for_manifest()
    manifest["pins"] = dict(sorted(pins.items()))
    manifest["provenance"]["statement_sha256"] = manifest["pins"]["Statement.lean"]
    manifest["paper_labels"][mainmap.PAGE] = main_labels(text)
    path.write_text(json.dumps(manifest, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    print(f"generated {mainmap.PAGE}: {sum(r['kind'] == 'lean' for r in recs)} Lean and "
          f"{sum(r['kind'] == 'paper' for r in recs)} paper blocks; closure {len(mm['closure']['declarations'])} "
          f"declarations")


if __name__ == "__main__":
    try:
        main()
    except mainmap.CheckError as error:
        sys.exit(f"FAIL {error}")
