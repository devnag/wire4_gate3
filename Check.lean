import Proof.Quartic.Release.Main
import Proof.Quartic.Reusable
import SourceAdapters.Vacuity.BCGT13Printed
import SourceAdapters.Vacuity.BCGT13Case2Distance
import SourceAdapters.Vacuity.BCGT13Case2Positive
import Lean.Util.CollectAxioms
open Lean Elab Command

/-! Run after `lake build`:  lake env lean Check.lean
It prints the paper's joint theorem as stated in Lean, the published results it assumes (the fields of
`PublishedInputs`) with their full statements and the definitions each one uses, the release theorem, the axioms of
the release theorem and of the main stages, and PASS or FAIL. -/

-- (a) The statement: the published results imply the joint theorem (`thm:main` and `thm:gates` of
-- `paper/paper.tex`). Its definitions are in `Statement.lean` and
-- `Proof/Quartic/Statement/{Final,Joint,Release}.lean`; `SourceMapping/main-theorem.md` prints all of them.
#print NearQuarticWires.Release.ReleaseStatement
#print NearQuarticWires.Statement.JointStatement4
#print NearQuarticWires.Statement.JointAt4
#print NearQuarticWires.Statement.WiresAt
#print NearQuarticWires.Statement.SymGatesAt
#print NearQuarticWires.Statement.GatesAt
#print NearQuarticWires.Statement.wireCap
#print NearQuarticWires.Statement.gateCap
#print NearQuarticWires.Statement.wires
#print NearQuarticWires.Statement.fanIn
#print NearQuarticWires.Statement.agr
#print NearCubicWires.SymmetricThresholdCircuit
#print NearCubicGates.Target.WeightedSymmetricCircuit
#print NearCubicGates.Target.lambda
#print NearCubicGates.Target.mu
#print NearCubicGates.Target.InENP

-- (b) The hypotheses: the published results, the fields of `PublishedInputs`, and each published statement.
#print NearCubicGates.Close.PublishedInputs
#print NearCubicGates.Published.Williams.RectangularProductLeaf
#print NearCubicGates.Published.BCGT13.BCGT13_Theorem11_1_Fixed
#print NearCubicGates.Published.Shoup.FindIrrPolyAlgorithm17
#print NearCubicGates.Published.STV.Theorem29
#print NearCubicGates.Published.CW19Proximity.Lemma22Half
#print NearCubicGates.Published.CW19Code.Lemma26

-- (c) For each published statement, the definitions of `Statement.lean` it uses (its closure).
run_cmd do
  let env ← getEnv
  let some stmt := env.getModuleIdx? `Statement | throwError "FAIL: module Statement not loaded"
  for f in getStructureFields env ``NearCubicGates.Close.PublishedInputs do
    let some p := env.find? (``NearCubicGates.Close.PublishedInputs ++ f) | throwError "FAIL: no projection {f}"
    let mut work : Array Name := p.type.getUsedConstants.filter (· != ``NearCubicGates.Close.PublishedInputs)
    let mut seen : NameSet := {}
    let mut names : Array Name := #[]
    while 0 < work.size do
      let n := work.back!
      work := work.pop
      if seen.contains n || env.getModuleIdxFor? n != some stmt then continue
      seen := seen.insert n
      unless n.isInternal || Meta.isMatcherCore env n do names := names.push n
      if let some ci := env.find? n then
        for u in ci.getUsedConstantsAsSet do work := work.push u
    let sorted := names.qsort (fun a b => a.toString < b.toString)
    IO.println s!"{f} uses {sorted.size} declarations of Statement.lean: {sorted.toList}"

-- (d) The release theorem `main_from_published` (`Solution.lean` gives it to comparator as `main_theorem`), its
-- axioms, and PASS only if: the release theorem is stated as `ReleaseStatement`;
-- `ReleaseStatement` is `PublishedInputs → JointStatement4`; the fields of `PublishedInputs` are exactly the published
-- statements below, in this order; `PublishedInputs` and every published statement are declared in `Statement.lean`,
-- `JointStatement4` in `Proof/Quartic/Statement/Joint.lean` and `ReleaseStatement` in
-- `Proof/Quartic/Statement/Release.lean`; and the axioms are exactly Lean's standard three.
run_cmd do
  let env ← getEnv
  let thm := `NearQuarticWires.Release.main_from_published
  let final := ``NearQuarticWires.Release.ReleaseStatement
  let inputs := ``NearCubicGates.Close.PublishedInputs
  let target := ``NearQuarticWires.Statement.JointStatement4
  let expected : List (Name × Expr) := [
    (`williams_rectangularProductLeaf, mkConst ``NearCubicGates.Published.Williams.RectangularProductLeaf []),
    (`bcgt13_theorem11_1, mkConst ``NearCubicGates.Published.BCGT13.BCGT13_Theorem11_1_Fixed []),
    (`shoup_findIrrPolyAlgorithm17, mkConst ``NearCubicGates.Published.Shoup.FindIrrPolyAlgorithm17 []),
    (`stv_theorem29, mkConst ``NearCubicGates.Published.STV.Theorem29 []),
    (`cw19Proximity_lemma22Half, mkConst ``NearCubicGates.Published.CW19Proximity.Lemma22Half []),
    (`cw19Code_lemma26, mkConst ``NearCubicGates.Published.CW19Code.Lemma26 [])]
  let std := #[``propext, ``Classical.choice, ``Quot.sound]
  let some stmt := env.getModuleIdx? `Statement | throwError "FAIL: module Statement not loaded"
  let some joint := env.getModuleIdx? `Proof.Quartic.Statement.Joint | throwError "FAIL: module Joint not loaded"
  let some rel := env.getModuleIdx? `Proof.Quartic.Statement.Release | throwError "FAIL: module Release not loaded"
  let some info := env.find? thm | throwError "FAIL: {thm} not found"
  IO.println s!"{thm} : {← liftTermElabM <| Meta.ppExpr info.type}"
  let okThm := info matches .thmInfo _ && info.type == mkConst final
  let okFinal := match env.find? final with
    | some (.defnInfo d) => match d.value with
      | .forallE _ dom body _ => dom == mkConst inputs && body == mkConst target
      | _ => false
    | _ => false
  let okStruct := match env.find? inputs with
    | some (.inductInfo i) => i.type == mkSort Level.zero && i.numParams == 0 && isStructure env inputs
    | _ => false
  let mut found : List (Name × Expr) := []
  for f in getStructureFields env inputs do
    let some p := env.find? (inputs ++ f) | throwError "FAIL: no projection {inputs ++ f}"
    let t := match p.type with
      | .forallE _ _ b _ => b
      | e => e
    found := found ++ [(f, t)]
    IO.println s!"assumes {f} : {← liftTermElabM <| Meta.ppExpr t}"
  let okInputs := okStruct && found == expected
  let trusted := [inputs] ++ expected.map (fun (_, e) => e.constName!)
  let okTrusted := trusted.all (fun n => env.getModuleIdxFor? n == some stmt) &&
    env.getModuleIdxFor? target == some joint && env.getModuleIdxFor? final == some rel
  let axs ← liftCoreM <| collectAxioms thm
  IO.println s!"axioms of {thm}: {axs.toList}"
  let okAxioms := axs.all std.contains && std.all axs.contains
  if okThm && okFinal && okInputs && okTrusted && okAxioms then
    IO.println s!"PASS: {thm} proves {final}: the {expected.length} published results above imply {target}; it depends on the axioms {axs.toList} only"
  else
    throwError "FAIL: stated as {final}: {okThm}; {final} = {inputs} → {target}: {okFinal}; the published results as listed: {okInputs}; declared in the statement files: {okTrusted}; axioms exactly propext, Classical.choice, Quot.sound: {okAxioms} ({axs.toList})"

-- (e) The axioms of the main stages of the proof.
#print axioms NearQuarticWires.Release.main_from_published
#print axioms NearQuarticWires.Release.release_of_stages
#print axioms NearQuarticWires.Program.counterExists4
#print axioms NearQuarticWires.Program.finalStatement4
#print axioms NearQuarticWires.Program.finalStatement4_of_stagesW
#print axioms NearQuarticWires.GateCorollary.jointStatement4_of_final
#print axioms NearQuarticWires.Transfer.transfer4_official
#print axioms NearQuarticWires.Reconstruct.reconstructControl
#print axioms NearCubicGates.Adapters.sources_to_nine
#print axioms NearCubicGates.Adapters.Assembly.Fixed.bcgt13Fixed_of_theorem11_1
-- The three corrections of printed BCGT13 listings, with checked witnesses (`SourceAdapters/Vacuity/BCGT13Printed.lean`).
#print axioms NearCubicGates.Adapters.Vacuity.BCGT13Printed.printed_and_corrected_differ
#print axioms NearCubicGates.Adapters.Vacuity.BCGT13Printed.swapped_honest_count
#print axioms NearCubicGates.Adapters.Vacuity.BCGT13Printed.actual_honest_count
#print axioms NearCubicGates.Adapters.Vacuity.BCGT13Printed.printed_base_not_interpolation
#print axioms NearCubicGates.Adapters.Vacuity.BCGT13Printed.intended_zero_interpolates
-- Checked comparison with Lemma 11.10's printed distance over a sixteen-element field.
#print axioms NearCubicGates.Adapters.Vacuity.BCGT13Case2Distance.field_card
#print axioms NearCubicGates.Adapters.Vacuity.BCGT13Case2Distance.field_binary_dimension
#print axioms NearCubicGates.Adapters.Vacuity.BCGT13Case2Distance.actual_distance
#print axioms NearCubicGates.Adapters.Vacuity.BCGT13Case2Distance.printed_case2_distance_counterexample
#print axioms NearCubicGates.Adapters.Vacuity.BCGT13Case2Positive.actual_distance_positive
#print axioms NearCubicGates.Adapters.Vacuity.BCGT13Case2Positive.positive_degree_distance_counterexample
#print axioms NearQuarticWires.Release.gate_paper_main

-- (f) The results of independent interest (`Proof/Quartic/Tomography.lean`, `Proof/Quartic/Reusable.lean`) and
-- their axioms.
#print axioms NearQuarticWires.Tomography.residueCounts_determine
#print axioms NearQuarticWires.Tomography.reconstruct
#print axioms NearQuarticWires.Tomography.reconstruct_at_side
#print axioms NearQuarticWires.Reusable.scalarCounts_determine
#print axioms NearQuarticWires.Reusable.scalar_reconstruct
#print axioms NearQuarticWires.Reusable.threshold_eq_newton_sum
#print axioms NearQuarticWires.Reusable.cycle_sum_identity
#print axioms NearQuarticWires.Reusable.mean_population
#print axioms NearQuarticWires.Reusable.wireTransfer
run_cmd do
  let std := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in [``NearQuarticWires.Release.gate_paper_main,
      ``NearQuarticWires.Tomography.residueCounts_determine, ``NearQuarticWires.Tomography.reconstruct,
      ``NearQuarticWires.Tomography.reconstruct_at_side, ``NearQuarticWires.Reusable.scalarCounts_determine,
      ``NearQuarticWires.Reusable.scalar_reconstruct, ``NearQuarticWires.Reusable.threshold_eq_newton_sum,
      ``NearQuarticWires.Reusable.cycle_sum_identity, ``NearQuarticWires.Reusable.mean_population,
      ``NearQuarticWires.Reusable.wireTransfer,
      ``NearCubicGates.Adapters.Assembly.Fixed.bcgt13Fixed_of_theorem11_1,
      ``NearCubicGates.Adapters.Vacuity.BCGT13Printed.printed_recurrence_witness,
      ``NearCubicGates.Adapters.Vacuity.BCGT13Printed.corrected_recurrence_witness,
      ``NearCubicGates.Adapters.Vacuity.BCGT13Printed.printed_and_corrected_differ,
      ``NearCubicGates.Adapters.Vacuity.BCGT13Printed.swapped_honest_count,
      ``NearCubicGates.Adapters.Vacuity.BCGT13Printed.actual_honest_count,
      ``NearCubicGates.Adapters.Vacuity.BCGT13Printed.printed_base_not_interpolation,
      ``NearCubicGates.Adapters.Vacuity.BCGT13Printed.intended_zero_interpolates,
      ``NearCubicGates.Adapters.Vacuity.BCGT13Case2Distance.field_card,
      ``NearCubicGates.Adapters.Vacuity.BCGT13Case2Distance.field_binary_dimension,
      ``NearCubicGates.Adapters.Vacuity.BCGT13Case2Distance.actual_distance,
      ``NearCubicGates.Adapters.Vacuity.BCGT13Case2Distance.printed_case2_distance_counterexample,
      ``NearCubicGates.Adapters.Vacuity.BCGT13Case2Positive.actual_distance_positive,
      ``NearCubicGates.Adapters.Vacuity.BCGT13Case2Positive.positive_degree_distance_counterexample] do
    let axs ← liftCoreM <| collectAxioms n
    unless axs.all std.contains do throwError "FAIL: {n} depends on {axs.toList}"
  IO.println "PASS: gate_paper_main, the results of independent interest and the BCGT13 witnesses use only propext, \
    Classical.choice and Quot.sound"
