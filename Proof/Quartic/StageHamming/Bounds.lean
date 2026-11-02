import Proof.Quartic.StageHamming.EncoderBlock

set_option autoImplicit false

namespace NearQuarticWires.StageHamming

open NearCubicGates.Close.Cells
open NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.Shared

/-- `imp:partition`, paper/paper.tex: the canonical
block length and its data and parity dimensions do not exceed the
original input arity. -/
theorem block_dimensions_le (P : StarParams) :
    P.b ≤ P.n ∧ P.s ≤ P.b ∧ PrimT.C4Geo.dB P ≤ P.b := by
  have hb : P.b ≤ P.n :=
    (show P.b ≤ P.r * P.b by
      simpa using Nat.mul_le_mul_right P.b (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt P.r_pos))).trans
      P.r_mul_b_le
  have hd := PrimT.C4Geo.dB_pos P
  change 1 ≤ P.b - P.s at hd
  exact ⟨hb, by omega, Nat.sub_le _ _⟩

/-- `imp:partition`, paper/paper.tex: the ordinary
binary width reserved by the original point producer accommodates all
linear scalar indices and boundary calculations used by the encoder. -/
theorem scalar_word_bound (P : StarParams) (W : ℕ) (hW : P.n + 4 ≤ W) :
    8 * (P.n + 1) < 2 ^ W := by
  calc
    _ < 8 * 2 ^ (P.n + 1) := Nat.mul_lt_mul_of_pos_left (Nat.lt_two_pow_self) (by decide)
    _ = 2 ^ (P.n + 4) := by
      rw [show P.n + 4 = (P.n + 1) + 3 by omega]
      simp only [pow_add]
      norm_num
      ring
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hW

/-- `imp:partition` and `prop:time`, paper/paper.tex: the complete scalar block encoder's actual lookup,
binary selection and xor costs are cubic in the original arity. -/
theorem encoderBlock_clock_le_arity (P : StarParams) (base : ℕ) (hbase : base ≤ P.n) :
    PrimT.C4Geo.dB P * (P.b * (8 * P.s + 24) + P.s * (5 * P.s + 21) +
      5 * (base + PrimT.C4Geo.dB P) + 84) + 6 ≤ 200 * (P.n + 1) ^ 3 := by
  obtain ⟨hb, hs, hd⟩ := block_dimensions_le P
  have hsn : P.s ≤ P.n := hs.trans hb
  have hdn : PrimT.C4Geo.dB P ≤ P.n := hd.trans hb
  have h1 : P.n ≤ (P.n + 1) ^ 3 := by
    have h := Nat.pow_le_pow_right (Nat.succ_pos P.n) (by decide : 1 ≤ 3)
    have h' : P.n + 1 ≤ (P.n + 1) ^ 3 := by simpa only [pow_one] using h
    exact (Nat.le_succ P.n).trans h'
  have h2 : P.n ^ 2 ≤ (P.n + 1) ^ 3 :=
    (Nat.pow_le_pow_left (Nat.le_succ P.n) 2).trans
      (Nat.pow_le_pow_right (Nat.succ_pos P.n) (by decide : 2 ≤ 3))
  have h3 : P.n ^ 3 ≤ (P.n + 1) ^ 3 := Nat.pow_le_pow_left (Nat.le_succ P.n) 3
  have h0 : 1 ≤ (P.n + 1) ^ 3 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  calc
    _ ≤ P.n * (P.n * (8 * P.n + 24) + P.n * (5 * P.n + 21) +
        5 * (P.n + P.n) + 84) + 6 := by gcongr
    _ = 13 * P.n ^ 3 + 55 * P.n ^ 2 + 84 * P.n + 6 := by ring
    _ ≤ _ := by omega

/-- `imp:partition` and `prop:time`, paper/paper.tex: the actual canonical block encoder fits the original
point producer's typed width and fixed cubic source clock. -/
theorem encoderBlock_arity_spec {C : Ctx} (a : DS VV MM) (hc : Cst a)
    (P : StarParams) (code base q : ℕ)
    (hlimit : a.env encoderLimit = PrimT.C4Geo.dB P)
    (hcode : a.env encoderCode = code) (hbase : a.env encoderBase = base)
    (hb : a.env dataLimit = P.b) (hswidth : a.env parityWidth = P.s)
    (hq : a.env columnTarget = q) (hbaseN : base ≤ P.n) (hqB : q < P.b)
    (hwidth : P.n + 4 ≤ C.Wd) :
    Hs C encoderBlock a (200 * (P.n + 1) ^ 3) (fun b =>
      b.env encoderAccumulator =
        (PrimT.C4Geo.encB P (fun m => code.testBit (base + m)) q).toNat ∧
      b.sh = a.sh ∧ Fr a b encoderLoopScratch) := by
  obtain ⟨hbN, hsB, hdB⟩ := block_dimensions_le P
  have hsmall := scalar_word_bound P C.Wd hwidth
  have hp := P.b_succ
  exact (encoderBlock_spec a hc P code base q hlimit hcode hbase hb hswidth hq
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).mono
      (encoderBlock_clock_le_arity P base hbaseN) (fun _ h => h)

end NearQuarticWires.StageHamming
