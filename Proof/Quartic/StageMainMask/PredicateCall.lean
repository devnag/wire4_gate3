import Proof.Quartic.StageMainMask.StructuralCall
import Proof.Quartic.StageMainMask.PredicateWriter

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageMain StageMain.Compact StageLift

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
the physically computed original point and literal complete call are
sent to the actual predicate machine and its framed bit is consumed. -/
def predicateStep : St VV MM :=
  .seq emitPredicateInput (.seq (.op .kcall) (readBitReply predicateValue))

/-- Step 4 of `sec:algorithm` and `prop:time`, paper/paper.tex: the complete original predicate,
including both original circuit tops, is evaluated by the actual cold
ordinary machine while the previous mask replies remain unchanged. -/
theorem predicateStep_run {B1 B2 : ℕ} (r : EntryRequest B1 B2)
    (width : ℕ) (input : List Bool) (L B : ℕ) (a : DS VV MM)
    (hc : Cst a) (ha : EntryNumericData r a) (hkin : a.kin = [])
    (hW : 2 ≤ width) (hcall : (callWord r.call).length < 2 ^ width)
    (hpoint : natBitLength (entryPredicateRequest r).point + 2 < 2 ^ width)
    (hL : 2 + (entryPredicateRequest r).word.length ≤ L)
    (hB : (entryCallee B1 B2).bud (.inr (.inr (entryPredicateRequest r))) ≤ B) :
    Hs (entryContext B1 B2 width input L B) predicateStep a
      (a.rc callStore + 8 * (callWord r.call).length +
        40 * natBitLength (entryPredicateRequest r).point + L + B + 70)
      (fun b => b.env predicateValue = (entryPredicate r).toNat ∧
        b.env structuralFlag = a.env structuralFlag ∧ b.env populationValue = a.env populationValue ∧
        b.kin = [] ∧ b.kout = frame [(entryPredicateRequest r).value] ∧ b.kc = 3 ∧
        b.ip = a.ip ∧ b.out = a.out ∧ b.ram = a.ram ∧ Cst b ∧
        EntryNumericData r b ∧ Fr a b entryEvaluationScratch) := by
  let C := entryContext B1 B2 width input L B
  unfold predicateStep
  refine (Hs.seq (t2 := (1 + L + B) + 5 + 1)
    (emitPredicateInput_run C r a hc ha hkin hW hcall hpoint hL) ?_).mono
      (by omega) (fun _ h => h)
  rintro b ⟨hbkin, hbi, hbo, hbm, _hbko, _hbkc, hbc, hbfr, _hbdata⟩
  have hin : b.kin = C.K.inw (.inr (.inr (entryPredicateRequest r))) := hbkin
  have hcall : Hs C (.op .kcall) b (1 + L + B)
      (fun d => d = b.called (frame [(entryPredicateRequest r).value])) :=
    Hs.op (OpEx.kcall (C := C) (.inr (.inr (entryPredicateRequest r))) b hin hB) rfl
  refine Hs.seq (t1 := 1 + L + B) (t2 := 5) hcall ?_
  rintro d rfl
  let d := b.called (frame [(entryPredicateRequest r).value])
  have hdc : Cst d := ⟨hbc.z, hbc.one, hbc.two⟩
  refine (readBitReply_run C predicateValue (by decide)
    (entryPredicateRequest r).value d hdc rfl rfl).mono le_rfl ?_
  rintro e ⟨hev, hekc, herest, hec, hefr⟩
  rcases (by simpa only [Prod.mk.injEq] using herest) with ⟨hei, heo, hem, _herc, hek, heko⟩
  have hef : Fr a e entryEvaluationScratch :=
    (hbfr.weaken (by
      intro x hx
      simp only [entryEvaluationScratch, List.mem_append]
      exact Or.inl (Or.inl hx))).trans (hefr.weaken (by decide))
  have herm : e.ram = a.ram := hem.trans hbm
  rw [entryPredicateRequest_value] at hev
  exact ⟨hev, (hefr _ (by decide)).trans (hbfr _ (by decide)),
    (hefr _ (by decide)).trans (hbfr _ (by decide)), hek, heko, hekc,
    hei.trans hbi, heo.trans hbo, herm, hec,
    ha.of_evaluation (congrFun herm _) (congrFun herm _) (congrFun herm _) hef, hef⟩

end NearQuarticWires.StageMainMask
