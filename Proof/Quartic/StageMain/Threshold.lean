import Proof.Quartic.StageMain.Weight

/-!
# Reading the threshold and deciding the gate

Paper: `def:class`, paper/paper.tex, and Step 4 of
`sec:algorithm`. The threshold is subtracted from the
signed score by adding its two parts to the opposite accumulators. The
comparison accepts equality, as required by the threshold convention.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces

def gateResult : Fin VV := ⟨47, by decide⟩
def thresholdUpdate : St VV :=
  .ite (.eq t8 vZ) (.op (.add scoreNegative t3)) (.op (.add scorePositive t3))

def compareScores : St VV := .ite (.lt scorePositive scoreNegative)
  (.op (.zero gateResult)) (.op (.copy gateResult v1))

def thresholdScratch : List (Fin VV) := [scorePositive, scoreNegative]

theorem thresholdUpdate_spec {C : Ctx} (a : DS VV) (hc : Cst a) (θ : ℤ)
    (hsg : a.env t8 = if θ < 0 then 1 else 0) (hmag : a.env t3 = θ.natAbs)
    (hcap : a.env scorePositive + a.env scoreNegative + θ.natAbs < 2 ^ C.Wd) :
    Hs C thresholdUpdate a 2 (fun b =>
      b.env scorePositive = a.env scorePositive + (-θ).toNat ∧
      b.env scoreNegative = a.env scoreNegative + θ.toNat ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b thresholdScratch) := by
  cases θ with
  | ofNat n =>
    have hs : (Cnd.eq t8 vZ).eval a = true := by simp [Cnd.eval, hsg, hc.z]
    refine Hs.mono (Hs.iteT (show t8 ≠ vZ by decide) hs
      (hs_add C scoreNegative t3 a (by decide) (by rw [hmag]; omega))) le_rfl ?_
    rintro b rfl
    refine ⟨?_, ?_, rfl, rfl, rfl, hc.set _ _ (by decide), Fr.set _ _ (by decide)⟩
    · simp (config := { decide := true })
    · simp [hmag]
  | negSucc n =>
    have hs : (Cnd.eq t8 vZ).eval a = false := by simp [Cnd.eval, hsg, hc.z]
    refine Hs.mono (Hs.iteF (show t8 ≠ vZ by decide) hs
      (hs_add C scorePositive t3 a (by decide) (by rw [hmag]; omega))) le_rfl ?_
    rintro b rfl
    refine ⟨?_, ?_, rfl, rfl, rfl, hc.set _ _ (by decide), Fr.set _ _ (by decide)⟩
    · simp [hmag]
    · simp (config := { decide := true })

theorem compareScores_spec {C : Ctx} (a : DS VV) (hc : Cst a) :
    Hs C compareScores a 2 (fun b =>
      b.env gateResult = (decide (a.env scoreNegative ≤ a.env scorePositive)).toNat ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b [gateResult]) := by
  refine Hs.ite (c := .lt scorePositive scoreNegative) (show scorePositive ≠ scoreNegative by decide)
    (fun h => ?_) (fun h => ?_)
  · have hh : a.env scorePositive < a.env scoreNegative := by simpa [Cnd.eval] using h
    refine Hs.mono (hs_zero C gateResult a) le_rfl ?_
    rintro b rfl
    exact ⟨by simp [not_le.mpr hh], rfl, rfl, rfl, hc.set _ _ (by decide), Fr.set _ _ (by decide)⟩
  · have hh : a.env scoreNegative ≤ a.env scorePositive := by simpa [Cnd.eval] using h
    refine Hs.mono (hs_copy C gateResult v1 a (by decide)) le_rfl ?_
    rintro b rfl
    exact ⟨by simp [hh, hc.one], rfl, rfl, rfl, hc.set _ _ (by decide), Fr.set _ _ (by decide)⟩

def finishGate : St VV := .seq readInt (.seq thresholdUpdate compareScores)
def finishGateScratch : List (Fin VV) := readIntT ++ [scorePositive, scoreNegative, gateResult]

theorem finishGate_spec {C : Ctx} (a : DS VV) (hc : Cst a) (θ : ℤ) (rest : List Bool)
    (hin : C.cw.drop a.cp = intWord θ ++ rest)
    (hW : C.cw.length + 2 ≤ C.Wd) (hL : C.cw.length + 2 < 2 ^ C.Wd)
    (hcap : a.env scorePositive + a.env scoreNegative + θ.natAbs < 2 ^ C.Wd) :
    Hs C finishGate a (60 * (intWord θ).length + 76) (fun b =>
      b.env gateResult = (decide (a.env scoreNegative + θ.toNat ≤ a.env scorePositive + (-θ).toNat)).toNat ∧
      b.cp = a.cp + (intWord θ).length ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      Fr a b finishGateScratch) := by
  refine Hx.hs (Hs.then (readInt_spec a hc θ rest hin hW hL)
    (fun b ⟨bs, bm, _, bp, bw, bo, bc, bf⟩ n1 hn1 => ?_))
  have bpos : b.env scorePositive = a.env scorePositive := bf _ (by decide)
  have bneg : b.env scoreNegative = a.env scoreNegative := bf _ (by decide)
  refine Hs.then (thresholdUpdate_spec b bc θ bs bm (by rw [bpos, bneg]; exact hcap))
    (fun d ⟨dp, dn, dcp, dw, dout, dc, df⟩ n2 hn2 => ?_)
  refine Hs.last (compareScores_spec d dc) ?_
  rintro e ⟨eb, ep, ew, eo, ec, ef⟩ n3 hn3
  refine ⟨⟨by rw [eb, dp, dn, bpos, bneg], by rw [ep, dcp, bp],
    by rw [ew, dw, bw], by rw [eo, dout, bo], ec,
    Fr.trans (bf.weaken (by decide)) (Fr.trans (df.weaken (by decide)) (ef.weaken (by decide)))⟩, by omega⟩

end NearQuarticWires.StageMain
