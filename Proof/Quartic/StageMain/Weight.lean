import Proof.Quartic.StageMain.ScoreUpdate
import Proof.Gates.Dispatch.Walk

/-!
# Evaluating one encoded input weight

Paper: `def:class`, paper/paper.tex, and Step 4 of
`sec:algorithm`. The program reads the next literal signed
weight, extracts the next packed input coordinate, and updates the two
nonnegative accumulators while preserving every other live scalar.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicGates.Close.Dispatch
open NearCubicGates.Close.Interfaces

def positiveContribution (w : ℤ) (x : ℕ) : ℕ := if x % 2 = 1 then w.toNat else 0
def negativeContribution (w : ℤ) (x : ℕ) : ℕ := if x % 2 = 1 then (-w).toNat else 0

def scoreWeight : St VV := .seq nextPointBit (.seq readInt scoreUpdate)
def scoreWeightScratch : List (Fin VV) := readIntT ++ [pointWork, pointBit, scorePositive, scoreNegative]

theorem scoreWeight_spec {C : Ctx} (a : DS VV) (hc : Cst a) (w : ℤ) (rest : List Bool)
    (hin : C.cw.drop a.cp = intWord w ++ rest)
    (hW : C.cw.length + 2 ≤ C.Wd) (hL : C.cw.length + 2 < 2 ^ C.Wd)
    (hpoint : a.env pointWork < 2 ^ C.Wd)
    (hcap : a.env scorePositive + a.env scoreNegative + w.natAbs < 2 ^ C.Wd) :
    Hs C scoreWeight a (60 * (intWord w).length + 125) (fun b =>
      b.env scorePositive = a.env scorePositive + positiveContribution w (a.env pointWork) ∧
      b.env scoreNegative = a.env scoreNegative + negativeContribution w (a.env pointWork) ∧
      b.env pointWork = a.env pointWork / 2 ∧
      b.cp = a.cp + (intWord w).length ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      FrS a b scoreWeightScratch) := by
  refine Hx.hs (Hs.then (nextPointBit_spec a hc (by omega) hpoint)
    (fun b ⟨bb, bx, bp, bw, bo, bc, bf⟩ n1 hn1 => ?_))
  have hi : C.cw.drop b.cp = intWord w ++ rest := by rw [bp]; exact hin
  refine Hs.then (readInt_spec b bc w rest hi hW hL)
    (fun c ⟨cs, cm, _, cp, cw, co, cc, cf⟩ n2 hn2 => ?_)
  have cbit : c.env pointBit = (decide (a.env pointWork % 2 = 1)).toNat := by
    rw [cf pointBit (by decide), bb]
    rcases Nat.mod_two_eq_zero_or_one (a.env pointWork) with hz | ho
    · simp [hz]
    · simp [ho]
  have cpos : c.env scorePositive = a.env scorePositive :=
    (cf _ (by decide)).trans (bf _ (by decide) (by decide))
  have cneg : c.env scoreNegative = a.env scoreNegative :=
    (cf _ (by decide)).trans (bf _ (by decide) (by decide))
  have cx : c.env pointWork = a.env pointWork / 2 := (cf _ (by decide)).trans bx
  refine Hs.last (scoreUpdate_spec c cc w (decide (a.env pointWork % 2 = 1)) cbit cs cm
    (by rw [cpos, cneg]; exact hcap)) ?_
  rintro e ⟨epos, eneg, ep, ew, eo, ec, ef⟩ n3 hn3
  refine ⟨⟨?_, ?_, (ef _ (by decide)).trans cx, by rw [ep, cp, bp],
    by rw [ew, cw, bw], by rw [eo, co, bo], ec, ?_⟩, by omega⟩
  · simpa only [cpos, positiveContribution, decide_eq_true_eq] using epos
  · simpa only [cneg, negativeContribution, decide_eq_true_eq] using eneg
  · exact FrS.trans (bf.weaken (by decide))
      (FrS.trans (cf.toS.weaken (by decide)) (ef.toS.weaken (by decide)))

end NearQuarticWires.StageMain
