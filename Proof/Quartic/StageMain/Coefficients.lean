import Proof.Quartic.StageMain.CoefficientsStart
import Proof.Quartic.StageMain.CoefficientsLoop

/-!
# Evaluating the literal list of top coefficients

Paper: `def:class`, paper/paper.tex, and Step 4 of
`sec:algorithm`. The coefficient list supplies both signed
parts of the top score and the absolute-weight offset used by the top
table. All capacity bounds follow from its actual serialized length.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicWires
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces

def evalCoefficients : St VV := .seq coefficientsStart coefficientLoop
def evalCoefficientsScratch : List (Fin VV) := coefficientsStartScratch ++ coefficientLoopScratch

theorem evalCoefficients_spec {C : Ctx} (ws : List ℤ) (rest : List Bool)
    (a : DS VV) (hc : Cst a) (hin : C.cw.drop a.cp = listWord intWord ws ++ rest)
    (hW : C.cw.length + 3 ≤ C.Wd) (hbits : a.env gateBits < 2 ^ C.Wd) :
    Hs C evalCoefficients a (200 * (C.cw.length + 2) ^ 2) (fun b =>
      b.env scorePositive = positiveScore ws (a.env gateBits) ∧
      b.env scoreNegative = negativeScore ws (a.env gateBits) ∧
      b.env topAbsolute = (ws.map Int.natAbs).sum ∧
      b.cp = a.cp + (listWord intWord ws).length ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      FrS a b evalCoefficientsScratch) := by
  have hi := hin
  simp only [listWord, List.append_assoc] at hi
  have hl := len_le_of_drop hin
  have hcount := length_le_flatMap ws intWord intWord_len_pos
  have hnb := natBitLength_le_len ws.length
  have hs := sum_natAbs_lt ws
  have hlen : (ws.flatMap intWord).length ≤ C.cw.length := by
    simp only [listWord, List.length_append] at hl
    omega
  have hnat : natBitLength ws.length ≤ C.cw.length := by
    simp only [listWord, List.length_append] at hl
    omega
  have hsum : (ws.map Int.natAbs).sum < 2 ^ C.cw.length :=
    hs.trans_le (Nat.pow_le_pow_right (by decide) hlen)
  have hpow : 8 * 2 ^ C.cw.length ≤ 2 ^ C.Wd := by
    have := Nat.pow_le_pow_right (show 1 ≤ (2 : ℕ) by decide) hW
    simpa [pow_add, Nat.mul_comm] using this
  have hL : C.cw.length + 2 < 2 ^ C.Wd := by
    have := Nat.lt_two_pow_self (n := C.Wd)
    omega
  refine Hx.hs (Hs.then (coefficientsStart_spec a hc ws.length _ hi (by omega) hL)
    (fun b ⟨bn, bi, bp, bneg, bx, ba, bcp, bw, bo, bc, bf⟩ n1 hn1 => ?_))
  have binput : C.cw.drop b.cp = ws.flatMap intWord ++ rest := by rw [bcp, drop_adv hi]
  have bcap : b.env scorePositive + b.env scoreNegative + b.env topAbsolute +
      3 * (ws.map Int.natAbs).sum + 1 < 2 ^ C.Wd := by
    rw [bp, bneg, ba]
    have := Nat.two_pow_pos C.cw.length
    omega
  refine Hs.last (coefficientLoop_spec ws rest b bc bi bn binput (by omega) hL (by omega)
    (by rw [bx]; exact hbits) bcap) ?_
  rintro e ⟨ep, en, _, ea, ecp, ew, eo, ec, ef, _, _⟩ n2 hn2
  refine ⟨⟨by rw [ep, bp, bx, Nat.zero_add], by rw [en, bneg, bx, Nat.zero_add],
    by rw [ea, ba, Nat.zero_add], ?_, ew.trans bw, eo.trans bo, ec,
    FrS.trans (bf.weaken (by decide)) (ef.weaken (by decide))⟩, ?_⟩
  · rw [ecp, bcp]
    simp only [listWord, List.length_append, Nat.add_assoc]
  · have hh := Nat.mul_le_mul_right (60 * C.cw.length + 131) (hcount.trans hlen)
    nlinarith only [hn1, hn2, hnat, hh]

end NearQuarticWires.StageMain
