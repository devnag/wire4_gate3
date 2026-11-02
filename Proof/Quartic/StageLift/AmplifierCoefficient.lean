import Proof.Quartic.StageCert.BinomialProgram
import Proof.Quartic.StageLift.DegreeProgram
import Proof.Quartic.StageLift.Token

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces.Formats StageCert.Tokens

/-- `imp:amp` and `lem:print`, paper/paper.tex: the actual amplifier summand's binary loop ordinal. -/
def amplifierIndex : Fin VV := 66

/-- `imp:amp`, `lem:certify`, paper/paper.tex: the exact integer
binomial numerator is formed and divided before any modular reduction. -/
def emitAmplifierCoefficient : St VV MM :=
  .seq (.op (.copy chooseN degreeExponent))
    (.seq (.op (.sub chooseN v1))
      (.seq (.op (.add chooseN amplifierIndex))
        (.seq (.op (.copy chooseR amplifierIndex))
          (.seq exactBinomial (emitNaturalConstant chooseValue)))))

/-- `imp:amp` and `lem:print`, paper/paper.tex: one actual BT coefficient token is computed from e
and the live ordinal, using exact integer division even for composite q. -/
theorem emitAmplifierCoefficient_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (e j B : ℕ) (he : 1 ≤ e) (hj : j < e)
    (heE : a.env degreeExponent = e) (hjJ : a.env amplifierIndex = j)
    (hroom : 2 ^ (2 * e) * (2 * e + 1) < 2 ^ C.Wd)
    (hW : 2 ≤ C.Wd)
    (hbits : natBitLength ((e - 1 + j).choose j) ≤ B)
    (hBit : B + 2 < 2 ^ C.Wd) :
    Hs C emitAmplifierCoefficient a (17 * j + 40 * B + 82) (fun b =>
      b.out = a.out ++ tokWord (.const (((e - 1 + j).choose j : ℕ) : ℤ)) ∧
      b.env chooseValue = (e - 1 + j).choose j ∧
      (b.ip, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.ip, a.ram, a.rc, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b (chooseN :: chooseR :: (binomialScratch ++ tokenScratch))) := by
  let n := e - 1 + j
  have hn : n ≤ 2 * e := by dsimp [n]; omega
  have hp : 1 ≤ 2 ^ (2 * e) := Nat.one_le_pow _ _ (by decide)
  have hsmall : 2 * e + 1 < 2 ^ C.Wd :=
    lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (by omega)) hroom
  have hbinomial : 2 ^ n * (n + 1) < 2 ^ C.Wd :=
    lt_of_le_of_lt (Nat.mul_le_mul
      (Nat.pow_le_pow_right (by decide) hn) (by omega)) hroom
  have htwo : 2 ≤ 2 ^ (2 * e) := by
    have h := Nat.pow_le_pow_right (show 1 ≤ (2 : ℕ) by decide) (show 1 ≤ 2 * e by omega)
    simpa using h
  have hden : 2 * (n + 1) ≤ 2 ^ C.Wd :=
    (Nat.mul_le_mul htwo (show n + 1 ≤ 2 * e + 1 by omega)).trans hroom.le
  unfold emitAmplifierCoefficient
  apply Hx.hs
  refine Hs.then (hs_copy C chooseN degreeExponent a (by decide))
    (fun b hb n1 hn1 => ?_)
  subst b
  let s1 := a.set chooseN (a.env degreeExponent)
  refine Hs.then (hs_sub C chooseN v1 s1 (by decide)
    (by dsimp [s1]; vsimp [heE, hc.one]; omega))
    (fun b hb n2 hn2 => ?_)
  subst b
  let s2 := s1.set chooseN (s1.env chooseN - s1.env v1)
  refine Hs.then (hs_add C chooseN amplifierIndex s2 (by decide)
    (by dsimp [s2, s1]; vsimp [heE, hjJ, hc.one]; omega))
    (fun b hb n3 hn3 => ?_)
  subst b
  let s3 := s2.set chooseN (s2.env chooseN + s2.env amplifierIndex)
  refine Hs.then (hs_copy C chooseR amplifierIndex s3 (by decide))
    (fun b hb n4 hn4 => ?_)
  subst b
  let s4 := s3.set chooseR (s3.env amplifierIndex)
  have hfr : Fr a s4 [chooseN, chooseR] :=
    (Fr.set a _ (by simp)).trans ((Fr.set s1 _ (by simp)).trans
      ((Fr.set s2 _ (by simp)).trans (Fr.set s3 _ (by simp))))
  have hnc : s4.env chooseN = n := by
    dsimp [s4, s3, s2, s1, n]
    vsimp [heE, hjJ, hc.one]
  have hrc : s4.env chooseR = j := by
    dsimp [s4, s3, s2, s1]
    vsimp [hjJ]
  have hs4 : Cst s4 := Cst.of_fr hc hfr (by decide)
  refine Hs.then (exactBinomial_run C s4 hs4 n j hnc hrc hbinomial hden)
    (fun d ⟨hdv, hdsh, hdc, hdf⟩ n5 hn5 => ?_)
  have hfit : natBitLength (d.env chooseValue) + 2 < 2 ^ C.Wd := by
    rw [hdv]
    exact lt_of_le_of_lt (by dsimp [n] at *; omega) hBit
  refine Hs.last (emitNaturalConstant_spec C chooseValue (by decide) (by decide) d hdc hW hfit)
    (fun z ⟨hzo, hzrest, hzc, hzf⟩ n6 hn6 => ?_)
  have hsame := Same.of_sh hdsh
  have hprefix : d.out = a.out := hsame.out
  have hf : Fr a z (chooseN :: chooseR :: (binomialScratch ++ tokenScratch)) :=
    (hfr.weaken (by simp)).trans ((hdf.weaken (by
      intro x hx
      simp only [List.mem_cons, List.mem_append] at hx ⊢
      tauto)).trans (hzf.weaken (by
        intro x hx
        simp only [List.mem_cons, List.mem_append]
        tauto)))
  refine ⟨⟨?_, ?_, ?_, hzc, hf⟩, ?_⟩
  · rw [hzo, hprefix, hdv]
  · rw [hzf chooseValue (by decide)]
    exact hdv
  · exact hzrest.trans (by rw [hsame.ip, hsame.ram, hsame.rc,
      hsame.kin, hsame.kout, hsame.kc]; rfl)
  · rw [hdv] at hn6
    have hm : min n j ≤ j := Nat.min_le_right _ _
    dsimp only [n] at hn6
    omega

end NearQuarticWires.StageLift
