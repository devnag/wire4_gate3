import Proof.Quartic.StageMainMask.StructuralRequest
import Proof.Quartic.StageMainMask.StructuralPrint
import Proof.Quartic.StageMain.CompactBounds
import Proof.Quartic.StageGamma.ReadFields

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageMain StageMain.Compact StageMain.Controller StageLift StageMain.CallSkip

/-- `def:mask` and Step 4 of `sec:algorithm`, paper/paper.tex: decode the actual finite preparation record
and then the two binary pattern indices from their original source. -/
def structuralPrepare : St VV MM :=
  .seq initializeCompact (StageGamma.readFields [structuralLeft, structuralRight])

/-- `prop:time`, paper/paper.tex: initialization and
the two pattern-field reads are charged by the exact source records. -/
noncomputable def structuralPrepareSteps {B1 B2 : ℕ} (r : StructuralRequest B1 B2) : ℕ :=
  initializeCost r.call r.selected.1 (Program.witnessPrefix r.call r.selected.1 r.witness)
    (compactInput r.call r.selected.1 (Program.witnessPrefix r.call r.selected.1 r.witness)).length +
  StageGamma.readFieldsCost [r.left.val, r.right.val] + 1

/-- `def:mask` and Step 4 of `sec:algorithm`, paper/paper.tex: all source data for the structural scan is
obtained by the actual preparation parser, with no initialized records
or decoded incidence data supplied by the caller. -/
theorem structuralPrepare_run {B1 B2 : ℕ} (C : Ctx) (r : StructuralRequest B1 B2)
    (rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = structuralWord r ++ rest)
    (hwidth : (structuralWord r).length + 2 ≤ C.Wd)
    (hempty : ∀ store, a.ram store = [] ∧ a.rc store = 0) :
    Hs C structuralPrepare a (structuralPrepareSteps r) (fun b =>
      PrintSource r.call r.selected.1 b ∧
      b.env lengthCounter = (callWord r.call).length ∧
      b.env structuralLeft = r.left.val ∧ b.env structuralRight = r.right.val ∧
      b.out = a.out ∧ Cst b) := by
  let witness := Program.witnessPrefix r.call r.selected.1 r.witness
  let prep := compactInput r.call r.selected.1 witness
  have hlayout : structuralWord r = prep ++ natWord r.left.val ++ natWord r.right.val := by
    rw [structuralWord, prepWord_eq_compact r.dispatched]
  have hpwidth : prep.length + 2 ≤ C.Wd := by
    rw [hlayout] at hwidth
    simp only [List.length_append] at hwidth
    omega
  obtain ⟨hprefix, hfit, hbits, hprime, hfactor⟩ :=
    compact_decoder_bounds r.call r.selected.1 witness C.Wd hpwidth
  have hi := initialize_run C r.call r.selected.1 prep.length witness
    (natWord r.left.val ++ natWord r.right.val ++ rest) a hc
    (by simpa only [hlayout, List.append_assoc] using hin)
    hprefix hfit hbits hpwidth ⟨hprime, hfactor⟩ (fun store _ => hempty store)
  obtain ⟨b, n, he, hn, hb⟩ := hi
  rcases hb with ⟨hbip, hbdata, _hblen, _hbram, _hbrc, hbrest, hbc, _hbfr⟩
  have hbcall : b.rc callStore ≤ (callWord r.call).length := by
    have hh := he.rc_le (by intro store; rw [(hempty store).1, (hempty store).2]; rfl) callStore
    rw [hbdata.originalCall, List.length_map] at hh
    exact hh
  have hbparam : b.rc parameterStore ≤ 46 := by
    have hh := he.rc_le (by intro store; rw [(hempty store).1, (hempty store).2]; rfl) parameterStore
    rw [hbdata.scalarFields, parameterScalars_length] at hh
    exact hh
  have hbinput : C.inp.drop b.ip = [r.left.val, r.right.val].flatMap natWord ++ rest := by
    rw [hbip, ← List.drop_drop, hin, hlayout]
    simp only [prep, List.append_assoc, List.drop_left, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
  have hfieldwidth : ∀ value ∈ [r.left.val, r.right.val], natBitLength value + 2 ≤ C.Wd := by
    intro value hv
    have hnbl := NearCubicGates.Close.Dispatch.natBitLength_le_len value
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rw [hlayout] at hwidth
    simp only [List.length_append] at hwidth
    rcases hv with rfl | rfl <;> omega
  have hread := StageGamma.readFields_spec C [structuralLeft, structuralRight]
    (by decide) (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> decide)
    [r.left.val, r.right.val] rfl b hbc rest hbinput hfieldwidth
  unfold structuralPrepare
  refine (Hs.seq (t2 := StageGamma.readFieldsCost [r.left.val, r.right.val])
    (show Hs C initializeCompact a
      (initializeCost r.call r.selected.1 witness prep.length) (· = b) from
      ⟨b, n, he, hn, rfl⟩) ?_).mono (by unfold structuralPrepareSteps; rfl) (fun _ h => h)
  intro e heq
  subst e
  refine hread.mono le_rfl ?_
  rintro d ⟨hdfields, _hdip, hdrest, hdc, hdfr⟩
  have hdram : d.ram = b.ram := congrArg (fun t => t.2.1) hdrest
  have hdrc : d.rc = b.rc := congrArg (fun t => t.2.2.1) hdrest
  have hdout : d.out = b.out := congrArg (fun t => t.1) hdrest
  have hbout : b.out = a.out := congrArg (fun t => t.1) hbrest
  refine ⟨⟨hdram ▸ hbdata.originalCall, hdram ▸ hbdata.scalarFields,
    hdrc ▸ hbcall, hdrc ▸ hbparam⟩,
    (hdfr _ (by decide)).trans hbdata.callBytes,
    ?_, ?_, hdout.trans hbout, hdc⟩
  · simpa only [Fin.getElem_fin, List.getElem_cons_zero] using hdfields ⟨0, by decide⟩
  · simpa only [Fin.getElem_fin, List.getElem_cons_succ, List.getElem_cons_zero] using hdfields ⟨1, by decide⟩

end NearQuarticWires.StageMainMask
