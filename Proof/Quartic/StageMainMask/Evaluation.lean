import Proof.Quartic.StageMainMask.PopulationCall
import Proof.Quartic.StageMainMask.PredicateCall
import Proof.Quartic.StageMainMask.ReplyBits

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageMain StageMain.Compact StageLift

/-- Step 4 of `sec:algorithm` and `prop:time`, paper/paper.tex: the scalar and ordinary-call
reservations for the three actual numeric-entry source requests. -/
structure EntryCallCapacity {B1 B2 : ℕ} (r : EntryRequest B1 B2) (width L B : ℕ) : Prop where
  minimum : 2 ≤ width
  prepared : (Program.prepWord B1 B2 r.call r.witness).length < 2 ^ width
  originalCall : (callWord r.call).length < 2 ^ width
  witness : (Program.witnessPrefix r.call r.selected.1 r.witness).length < 2 ^ width
  left : natBitLength (entryPosition r).1.val + 2 < 2 ^ width
  right : natBitLength (entryPosition r).2.val + 2 < 2 ^ width
  metadata : ∀ p ∈ populationInputFields r, natBitLength p.2 + 2 < 2 ^ width
  predicate : natBitLength (entryPredicateRequest r).point + 2 < 2 ^ width
  population : natBitLength (entryPopulationRequest r).value + 2 ≤ width
  structuralInput : 1 + (structuralWord (entryStructuralRequest r)).length ≤ L
  populationInput : 2 + (entryPopulationRequest r).word.length ≤ L
  predicateInput : 2 + (entryPredicateRequest r).word.length ≤ L
  structuralTime : (entryCallee B1 B2).bud (.inl (entryStructuralRequest r)) ≤ B
  populationTime : (entryCallee B1 B2).bud (.inr (.inl (entryPopulationRequest r))) ≤ B
  predicateTime : (entryCallee B1 B2).bud (.inr (.inr (entryPredicateRequest r))) ≤ B

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
one physical body evaluates the shared structural flag, complete
original selected population and original predicate, compares the
integer cutoff and writes the two actual reply payload bits. -/
def evaluateEntry : St VV MM := .seq structuralStep
  (.seq populationStep (.seq predicateStep (.seq compareMask emitReplyBits)))

/-- `prop:time`, paper/paper.tex: every original
source copy, binary scalar emission, ordinary call, framed reply read
and the final integer comparison contributes to this native clock. -/
noncomputable def evaluationSteps {B1 B2 : ℕ} (r : EntryRequest B1 B2) (L B : ℕ) : ℕ :=
  9 * (Program.prepWord B1 B2 r.call r.witness).length + 18 * (callWord r.call).length +
    11 * (Program.witnessPrefix r.call r.selected.1 r.witness).length +
    40 * natBitLength (entryPosition r).1.val + 40 * natBitLength (entryPosition r).2.val +
    40 * natBitLength (entryPredicateRequest r).point + naturalFieldsCost (populationInputFields r) +
    9 * (natWord (entryPopulationRequest r).value).length +
    30 * natBitLength (entryPopulationRequest r).value + 3 * L + 3 * B + 300

/-- `def:mask`, Step 4 of `sec:algorithm` and `prop:time`,
paper/paper.tex:
the three actual ordinary subroutines are physically composed, and
the final bits are exactly the required complete original predicate
and mask, with all source and reply work included in the native clock. -/
theorem evaluateEntry_run {B1 B2 : ℕ} (r : EntryRequest B1 B2)
    (width : ℕ) (input : List Bool) (L B : ℕ) (a : DS VV MM)
    (hc : Cst a) (ha : EntryNumericData r a) (hkin : a.kin = [])
    (hcur : ∀ store, a.rc store ≤ (a.ram store).length)
    (hempty : a.ram populationReplyStore = []) (hcap : EntryCallCapacity r width L B) :
    Hs (entryContext B1 B2 width input L B) evaluateEntry a (evaluationSteps r L B)
      (fun b => b.out = a.out ++ [entryPredicate r, entryMask r]) := by
  let C := entryContext B1 B2 width input L B
  obtain ⟨b, ns, hes, hns, hbflag, hbkin, _hbko, _hbkc, _hbi, hbo, hbm, hbc, hbdata, _hbfr⟩ :=
    structuralStep_run r width input L B a hc ha hkin hcap.minimum hcap.prepared
      hcap.left hcap.right hcap.structuralInput hcap.structuralTime
  have hbcur := hes.rc_le hcur
  obtain ⟨c, np, hep, hnp, hcpop, hcs, hckin, _hcko, _hckc, _hci, hco, _hcm,
      hcc, hcdata, _hcfr⟩ :=
    populationStep_run r width input L B b hbc hbdata hbkin hbcur
      ((congrFun hbm _).trans hempty) hcap.minimum hcap.originalCall hcap.witness
      hcap.metadata hcap.population hcap.populationInput hcap.populationTime
  have hccur := hep.rc_le hbcur
  obtain ⟨d, nv, hev, hnv, hdpred, hds, hdp, _hdkin, _hdko, _hdkc, _hdi, hdo,
      _hdm, hdc, hddata, _hdfr⟩ :=
    predicateStep_run r width input L B c hcc hcdata hckin hcap.minimum hcap.originalCall
      hcap.predicate hcap.predicateInput hcap.predicateTime
  obtain ⟨e, nm, hem, hnm, hemask, hesh, hec, hefr⟩ :=
    compareMask_run C d hdc (structuralBit (entryStructuralRequest r))
      (entryPopulationRequest r).value r.selected.1.tau
      (hds.trans (hcs.trans hbflag)) (hdp.trans hcpop) hddata.cutoff
  have hemp : e.env numericMaskValue = (entryMask r).toNat := by
    rw [entryMask_eq_replies]
    exact hemask
  have hepred : e.env predicateValue = (entryPredicate r).toNat :=
    (hefr _ (by decide)).trans hdpred
  obtain ⟨f, no, heo, hno, hfo⟩ := emitReplyBits_run C e hec _ _ hepred hemp
  have hscursor : a.rc compactStore ≤ (Program.prepWord B1 B2 r.call r.witness).length := by
    simpa only [ha.prepared, List.length_map] using hcur compactStore
  have hpcursor : b.rc callStore ≤ (callWord r.call).length := by
    simpa only [hbdata.originalCall, List.length_map] using hbcur callStore
  have hpwcursor : b.rc witnessStore ≤ (Program.witnessPrefix r.call r.selected.1 r.witness).length := by
    simpa only [hbdata.witness, List.length_map] using hbcur witnessStore
  have hvcursor : c.rc callStore ≤ (callWord r.call).length := by
    simpa only [hcdata.originalCall, List.length_map] using hccur callStore
  unfold evaluateEntry
  refine ⟨f, ns + (np + (nv + (nm + no + 1) + 1) + 1) + 1,
    Ex.seq hes (Ex.seq hep (Ex.seq hev (Ex.seq hem heo))), ?_, ?_⟩
  · unfold evaluationSteps
    omega
  · have heout := (Same.of_sh hesh).out
    change f.out = a.out ++ [entryPredicate r, entryMask r]
    rw [hfo, heout, hdo, hco, hbo]

end NearQuarticWires.StageMainMask
