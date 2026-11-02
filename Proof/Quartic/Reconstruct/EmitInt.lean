import Proof.Quartic.Reconstruct.Emit

/-!
# Writing a shifted integer in the cell language

The coordinates of the points of a box are integers `y = x - B` held as two natural numbers (the shifted coordinate
`x = y + B` and the shift `B`, `BoxArith.boxAxisOf_eq`). `emitShiftD_spec` writes `intWord (x - B)` (the sign word,
then the magnitude) at depth `d` of marks.
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells

variable {C : Ctx}

theorem natBitLength_mono {x y : ℕ} (h : x ≤ y) : natBitLength x ≤ natBitLength y := by
  unfold natBitLength
  have := Nat.log_mono_right (b := 2) h
  omega

theorem one_le_natBitLength (x : ℕ) : 1 ≤ natBitLength x := by unfold natBitLength; omega

/-- Write `intWord (x - B)` at depth `d`, for natural numbers `x`, `B` held in the variables `x`, `B`. -/
def emitShiftD (d : ℕ) (x B : Fin VV) : St VV MM :=
  .ite (.lt x B)
    (.seq (.op (.zero t3)) (.seq (.op (.inc t3)) (.seq (emitNatD d) (.seq (.op (.copy t3 B))
      (.seq (.op (.sub t3 x)) (emitNatD d))))))
    (.seq (.op (.zero t3)) (.seq (emitNatD d) (.seq (.op (.copy t3 x)) (.seq (.op (.sub t3 B)) (emitNatD d)))))

/-- The scratch variables of `emitShiftD`. -/
def emitShiftT : List (Fin VV) := t3 :: emitNatDT

/-- The cost of `emitShiftD d` on values of total bit length `ℓ`. -/
def emitShiftCost (d ℓ : ℕ) : ℕ := 2 * emitNatDCost d ℓ + 12

theorem emitShiftD_spec (d : ℕ) (x B : Fin VV) (hxB : x ≠ B) (hx : x ∉ emitShiftT) (hB : B ∉ emitShiftT)
    (a : DS VV MM) (hc : Cst a) (hW : 2 ≤ C.Wd)
    (hv : natBitLength (a.env x + a.env B) + 2 < 2 ^ C.Wd) :
    Hs C (emitShiftD d x B) a (emitShiftCost d (natBitLength (a.env x + a.env B)))
      (fun b => Wrote a b (marksD d (NearCubicGates.Close.Interfaces.intWord ((a.env x : ℤ) - a.env B)))
        emitShiftT ∧ Cst b) := by
  set X := a.env x with hX
  set Bv := a.env B with hBv
  set ℓ := natBitLength (X + Bv) with hℓ
  have hsub : ∀ y ∈ emitNatDT, y ∈ emitShiftT := fun y hy => List.mem_cons_of_mem _ hy
  have h3T : t3 ∈ emitShiftT := by decide
  have hx3 : x ≠ t3 := fun h => hx (by rw [h]; exact h3T)
  have hB3 : B ≠ t3 := fun h => hB (by rw [h]; exact h3T)
  have hxN : x ∉ emitNatDT := fun h => hx (hsub x h)
  have hBN : B ∉ emitNatDT := fun h => hB (hsub B h)
  have hp : 1 ≤ 2 ^ d := Nat.one_le_two_pow
  have h2W : 2 ≤ 2 ^ C.Wd := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hnb1 : natBitLength 1 = 1 := by simp [natBitLength]
  have hnb0 : natBitLength 0 = 1 := by simp [natBitLength]
  have hℓ1 : 1 ≤ ℓ := one_le_natBitLength _
  have kc : ∀ m, m ≤ ℓ → emitNatDCost d m ≤ emitNatDCost d ℓ := by
    intro m hm
    unfold emitNatDCost
    exact Nat.mul_le_mul_left _ (by omega)
  refine Hs.ite (c := .lt x B) hxB (fun he => ?_) (fun he => ?_)
  · -- `x < B`: the sign `1`, then `B - x`
    have hlt : X < Bv := by simpa [Cnd.eval] using he
    refine Hx.hs (Hs.then (hs_zero C t3 a) (fun b0 hb0 n0 hn0 => ?_))
    subst hb0
    refine Hs.then (hs_inc C t3 _ (by vsimp []; omega)) (fun b1 hb1 n1 hn1 => ?_)
    subst hb1
    have c1 : Cst ((a.set t3 0).set t3 ((a.set t3 0).env t3 + 1)) :=
      ⟨by vsimp [hc.z], by vsimp [hc.one], by vsimp [hc.two]⟩
    have e1 : ((a.set t3 0).set t3 ((a.set t3 0).env t3 + 1)).env t3 = 1 := by vsimp []
    refine Hs.then (emitNatD_spec d _ c1 hW (by rw [e1, hnb1]; omega)) (fun b2 hb2 n2 hn2 => ?_)
    obtain ⟨w2, c2⟩ := hb2
    try rw [e1] at w2
    try rw [e1] at hn2
    try rw [hnb1] at hn2
    have b2B : b2.env B = Bv := by
      rw [w2.fr B hBN, DS.set_env_ne _ _ hB3, DS.set_env_ne _ _ hB3]
    have b2x : b2.env x = X := by
      rw [w2.fr x hxN, DS.set_env_ne _ _ hx3, DS.set_env_ne _ _ hx3]
    refine Hs.then (hs_copy C t3 B b2 hB3.symm) (fun b3 hb3 n3 hn3 => ?_)
    subst hb3
    have hs4 : (b2.set t3 (b2.env B)).env x ≤ (b2.set t3 (b2.env B)).env t3 := by
      rw [DS.set_env_ne _ _ hx3, DS.set_env_self, b2B, b2x]; omega
    refine Hs.then (hs_sub C t3 x _ hx3.symm hs4) (fun b4 hb4 n4 hn4 => ?_)
    subst hb4
    have e4 : ((b2.set t3 (b2.env B)).set t3 ((b2.set t3 (b2.env B)).env t3 -
        (b2.set t3 (b2.env B)).env x)).env t3 = Bv - X := by
      rw [DS.set_env_self, DS.set_env_ne _ _ hx3, DS.set_env_self, b2B, b2x]
    have c4 : Cst ((b2.set t3 (b2.env B)).set t3 ((b2.set t3 (b2.env B)).env t3 -
        (b2.set t3 (b2.env B)).env x)) := ⟨by vsimp [c2.z], by vsimp [c2.one], by vsimp [c2.two]⟩
    have hlB : natBitLength (Bv - X) ≤ ℓ := natBitLength_mono (by omega)
    refine Hs.last (emitNatD_spec d _ c4 hW (by rw [e4]; omega)) (fun b5 hb5 n5 hn5 => ?_)
    obtain ⟨w5, c5⟩ := hb5
    try rw [e4] at w5
    try rw [e4] at hn5
    refine ⟨⟨?_, c5⟩, ?_⟩
    · have hw := ((((Wrote.refl a emitShiftT).set _ h3T).set _ h3T).trans (w2.weaken hsub)).trans
        ((((Wrote.refl b2 emitShiftT).set _ h3T).set _ h3T).trans (w5.weaken hsub))
      have hint : NearCubicGates.Close.Interfaces.intWord ((X : ℤ) - Bv) = natWord 1 ++ natWord (Bv - X) := by
        unfold NearCubicGates.Close.Interfaces.intWord
        rw [if_pos (by omega)]
        congr 2
        omega
      rw [hint, marksD_append]
      simpa using hw
    · have k1 := kc 1 hℓ1
      have k2 := kc _ hlB
      omega
  · -- `B ≤ x`: the sign `0`, then `x - B`
    have hle : Bv ≤ X := by simpa [Cnd.eval] using he
    refine Hx.hs (Hs.then (hs_zero C t3 a) (fun b0 hb0 n0 hn0 => ?_))
    subst hb0
    have c0 : Cst (a.set t3 0) := ⟨by vsimp [hc.z], by vsimp [hc.one], by vsimp [hc.two]⟩
    have e0 : (a.set t3 0).env t3 = 0 := by vsimp []
    refine Hs.then (emitNatD_spec d _ c0 hW (by rw [e0, hnb0]; omega)) (fun b2 hb2 n2 hn2 => ?_)
    obtain ⟨w2, c2⟩ := hb2
    try rw [e0] at w2
    try rw [e0] at hn2
    try rw [hnb0] at hn2
    have b2B : b2.env B = Bv := by
      rw [w2.fr B hBN, DS.set_env_ne _ _ hB3]
    have b2x : b2.env x = X := by
      rw [w2.fr x hxN, DS.set_env_ne _ _ hx3]
    refine Hs.then (hs_copy C t3 x b2 hx3.symm) (fun b3 hb3 n3 hn3 => ?_)
    subst hb3
    have hs4 : (b2.set t3 (b2.env x)).env B ≤ (b2.set t3 (b2.env x)).env t3 := by
      rw [DS.set_env_ne _ _ hB3, DS.set_env_self, b2B, b2x]; omega
    refine Hs.then (hs_sub C t3 B _ hB3.symm hs4) (fun b4 hb4 n4 hn4 => ?_)
    subst hb4
    have e4 : ((b2.set t3 (b2.env x)).set t3 ((b2.set t3 (b2.env x)).env t3 -
        (b2.set t3 (b2.env x)).env B)).env t3 = X - Bv := by
      rw [DS.set_env_self, DS.set_env_ne _ _ hB3, DS.set_env_self, b2B, b2x]
    have c4 : Cst ((b2.set t3 (b2.env x)).set t3 ((b2.set t3 (b2.env x)).env t3 -
        (b2.set t3 (b2.env x)).env B)) := ⟨by vsimp [c2.z], by vsimp [c2.one], by vsimp [c2.two]⟩
    have hlB : natBitLength (X - Bv) ≤ ℓ := natBitLength_mono (by omega)
    refine Hs.last (emitNatD_spec d _ c4 hW (by rw [e4]; omega)) (fun b5 hb5 n5 hn5 => ?_)
    obtain ⟨w5, c5⟩ := hb5
    try rw [e4] at w5
    try rw [e4] at hn5
    refine ⟨⟨?_, c5⟩, ?_⟩
    · have hw := (((Wrote.refl a emitShiftT).set _ h3T).trans (w2.weaken hsub)).trans
        ((((Wrote.refl b2 emitShiftT).set _ h3T).set _ h3T).trans (w5.weaken hsub))
      have hint : NearCubicGates.Close.Interfaces.intWord ((X : ℤ) - Bv) = natWord 0 ++ natWord (X - Bv) := by
        unfold NearCubicGates.Close.Interfaces.intWord
        rw [if_neg (by omega)]
        congr 2
        omega
      rw [hint, marksD_append]
      simpa using hw
    · have k1 := kc 1 hℓ1
      have k2 := kc _ hlB
      omega

end NearQuarticWires.Reconstruct
