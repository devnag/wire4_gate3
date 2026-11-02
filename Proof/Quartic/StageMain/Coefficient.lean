import Proof.Quartic.StageMain.Weight

/-!
# Reading one signed top coefficient

Paper: `def:class`, paper/paper.tex, and Step 4 of
`sec:algorithm`. The next bottom-gate bit selects the
coefficient's contribution to the signed top score. The absolute value
is also accumulated to obtain the table's literal index offset.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces

def topAbsolute : Fin VV := ⟨54, by decide⟩
def coefficientStep : St VV :=
  .seq nextPointBit (.seq readInt (.seq scoreUpdate (.op (.add topAbsolute t3))))
def coefficientScratch : List (Fin VV) := topAbsolute :: scoreWeightScratch

theorem coefficientStep_spec {C : Ctx} (a : DS VV) (hc : Cst a) (w : ℤ) (rest : List Bool)
    (hin : C.cw.drop a.cp = intWord w ++ rest)
    (hW : C.cw.length + 2 ≤ C.Wd) (hL : C.cw.length + 2 < 2 ^ C.Wd)
    (hpoint : a.env pointWork < 2 ^ C.Wd)
    (hcap : a.env scorePositive + a.env scoreNegative + w.natAbs < 2 ^ C.Wd)
    (hab : a.env topAbsolute + w.natAbs < 2 ^ C.Wd) :
    Hs C coefficientStep a (60 * (intWord w).length + 127) (fun b =>
      b.env scorePositive = a.env scorePositive + positiveContribution w (a.env pointWork) ∧
      b.env scoreNegative = a.env scoreNegative + negativeContribution w (a.env pointWork) ∧
      b.env pointWork = a.env pointWork / 2 ∧ b.env topAbsolute = a.env topAbsolute + w.natAbs ∧
      b.cp = a.cp + (intWord w).length ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      FrS a b coefficientScratch) := by
  refine Hx.hs (Hs.then (nextPointBit_spec a hc (by omega) hpoint)
    (fun b ⟨bb, bx, bp, bw, bo, bc, bf⟩ n1 hn1 => ?_))
  have binput : C.cw.drop b.cp = intWord w ++ rest := by rw [bp]; exact hin
  refine Hs.then (readInt_spec b bc w rest binput hW hL)
    (fun d ⟨ds, dm, _, dp, dw, dout, dc, df⟩ n2 hn2 => ?_)
  have dpos : d.env scorePositive = a.env scorePositive :=
    (df _ (by decide)).trans (bf _ (by decide) (by decide))
  have dneg : d.env scoreNegative = a.env scoreNegative :=
    (df _ (by decide)).trans (bf _ (by decide) (by decide))
  have dab : d.env topAbsolute = a.env topAbsolute :=
    (df _ (by decide)).trans (bf _ (by decide) (by decide))
  let bit := decide (a.env pointWork % 2 = 1)
  have dbit : d.env pointBit = bit.toNat := by
    rw [df _ (by decide), bb]
    rcases Nat.mod_two_eq_zero_or_one (a.env pointWork) with hz | ho
    · simp [bit, hz]
    · simp [bit, ho]
  refine Hs.then (scoreUpdate_spec d dc w bit dbit ds dm (by rw [dpos, dneg]; exact hcap))
    (fun e ⟨epos, eneg, ep, ew, eo, ec, ef⟩ n3 hn3 => ?_)
  have em : e.env t3 = w.natAbs := (ef _ (by decide)).trans dm
  have eab : e.env topAbsolute = a.env topAbsolute := (ef _ (by decide)).trans dab
  refine Hs.last (hs_add C topAbsolute t3 e (by decide) (by rw [em, eab]; exact hab)) ?_
  rintro f rfl n4 hn4
  refine ⟨⟨?_, ?_, ?_, ?_, by rw [DS.set_cp, ep, dp, bp], by rw [DS.set_wq, ew, dw, bw],
    by rw [DS.set_out, eo, dout, bo], ec.set _ _ (by decide),
    FrS.trans (bf.weaken (by decide))
      (FrS.trans (df.toS.weaken (by decide))
        (FrS.trans (ef.toS.weaken (by decide)) (Fr.set _ _ (by decide)).toS))⟩, by omega⟩
  · simpa (config := { decide := true }) [positiveContribution, bit, dpos] using epos
  · simpa (config := { decide := true }) [negativeContribution, bit, dneg] using eneg
  · simpa (config := { decide := true }) using
      (ef _ (by decide)).trans ((df _ (by decide)).trans bx)
  · simp [em, eab]

end NearQuarticWires.StageMain
