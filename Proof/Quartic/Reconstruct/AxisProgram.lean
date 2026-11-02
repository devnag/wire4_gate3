import Proof.Quartic.Reconstruct.Horner

/-!
# The coordinate interval of a box in the cell language

Paper: `lem:certify`(d), paper/paper.tex.

From `M_1`, `A`, `Λ`, the bound `B = 2mG_j` and the two Horner values `K^±` of a digit vector, `axisS` computes the
shifted start `lo' = (M_1K⁺ + A + AB ∸ (M_1K⁻ + Λ)) / A` and the number of points
`min((M_1K⁺ + (Λ - 1) + AB + A ∸ M_1K⁻) / A, 2B + 1) ∸ lo'` of the coordinate interval (`axisS_spec`), the
quantities of `BoxArith.boxAxisOf_eq`.
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicGates.Close.Cells

variable {C : Ctx}

/-! ## Truncated subtraction and minimum -/

/-- `x := x ∸ y`. -/
def tsubS (x y : Fin VV) : St VV MM := .ite (.lt x y) (.op (.zero x)) (.op (.sub x y))

theorem tsubS_spec (x y : Fin VV) (hxy : x ≠ y) (a : DS VV MM) :
    Hs C (tsubS x y) a 2 (· = a.set x (a.env x - a.env y)) := by
  refine Hs.ite (c := .lt x y) hxy (fun he => ?_) (fun he => ?_)
  · have h : a.env x < a.env y := by simpa [Cnd.eval] using he
    refine Hs.mono (hs_zero C x a) (by norm_num) ?_
    rintro b rfl
    rw [show a.env x - a.env y = 0 by omega]
  · have h : ¬ a.env x < a.env y := by simpa [Cnd.eval] using he
    exact Hs.mono (hs_sub C x y a hxy (by omega)) (by norm_num) (fun b hb => hb)

/-- `x := min x y`. -/
def minS (x y : Fin VV) : St VV MM := .ite (.lt x y) (.op (.add x vZ)) (.op (.copy x y))

theorem minS_spec (x y : Fin VV) (hxy : x ≠ y) (hxZ : x ≠ vZ) (a : DS VV MM) (hc : Cst a)
    (hx : a.env x < 2 ^ C.Wd) :
    Hs C (minS x y) a 2 (· = a.set x (min (a.env x) (a.env y))) := by
  refine Hs.ite (c := .lt x y) hxy (fun he => ?_) (fun he => ?_)
  · have h : a.env x < a.env y := by simpa [Cnd.eval] using he
    refine Hs.mono (hs_add C x vZ a hxZ (by rw [hc.z]; simpa using hx)) (by norm_num) ?_
    rintro b rfl
    rw [hc.z, Nat.add_zero, min_eq_left h.le]
  · have h : ¬ a.env x < a.env y := by simpa [Cnd.eval] using he
    refine Hs.mono (hs_copy C x y a hxy) (by norm_num) ?_
    rintro b rfl
    rw [min_eq_right (by omega)]

/-! ## The interval -/

/-- Input `M_1`. -/
def aM : Fin VV := ⟨25, by decide⟩
/-- Input `A`. -/
def aA : Fin VV := ⟨26, by decide⟩
/-- Input `Λ`. -/
def aL : Fin VV := ⟨27, by decide⟩
/-- Input `B`. -/
def aB : Fin VV := ⟨28, by decide⟩
/-- Input `K⁺`. -/
def aHp : Fin VV := ⟨29, by decide⟩
/-- Input `K⁻`. -/
def aHn : Fin VV := ⟨30, by decide⟩
/-- Output: the shifted start `lo'`. -/
def vLo : Fin VV := ⟨31, by decide⟩
/-- Output: the number of points. -/
def vLen : Fin VV := ⟨32, by decide⟩
/-- Scratch. -/
def xP1 : Fin VV := ⟨33, by decide⟩
/-- Scratch. -/
def xP2 : Fin VV := ⟨34, by decide⟩
/-- Scratch. -/
def xP3 : Fin VV := ⟨35, by decide⟩
/-- Scratch. -/
def xX : Fin VV := ⟨36, by decide⟩
/-- Scratch. -/
def xY : Fin VV := ⟨37, by decide⟩
/-- Scratch. -/
def xR : Fin VV := ⟨38, by decide⟩
/-- Scratch. -/
def xQ : Fin VV := ⟨39, by decide⟩
/-- Scratch. -/
def xC : Fin VV := ⟨40, by decide⟩

/-- The program of the coordinate interval. -/
def axisS : St VV MM :=
  .seq (.op (.mul aM aHp xP1)) (.seq (.op (.mul aA aB xP2)) (.seq (.op (.mul aM aHn xP3))
  (.seq (.op (.copy xX xP1)) (.seq (.op (.add xX aA)) (.seq (.op (.add xX xP2))
  (.seq (.op (.copy xY xP3)) (.seq (.op (.add xY aL)) (.seq (tsubS xX xY) (.seq (.op (.dm xX aA vLo xR))
  (.seq (.op (.copy xX xP1)) (.seq (.op (.add xX aL)) (.seq (.op (.sub xX v1)) (.seq (.op (.add xX xP2))
  (.seq (.op (.add xX aA)) (.seq (tsubS xX xP3) (.seq (.op (.dm xX aA xQ xR))
  (.seq (.op (.copy xC aB)) (.seq (.op (.shl xC)) (.seq (.op (.inc xC)) (.seq (minS xQ xC)
  (.seq (.op (.copy vLen xQ)) (tsubS vLen vLo))))))))))))))))))))))

/-- The variables written by `axisS`. -/
def axisT : List (Fin VV) := [vLo, vLen, xP1, xP2, xP3, xX, xY, xR, xQ, xC]

/-- **The coordinate interval.** -/
theorem axisS_spec (a : DS VV MM) (hc : Cst a) (M A L B Hp Hn : ℕ) (hM : a.env aM = M) (hA : a.env aA = A)
    (hL : a.env aL = L) (hB : a.env aB = B) (hHp : a.env aHp = Hp) (hHn : a.env aHn = Hn) (hA1 : 1 ≤ A)
    (hL1 : 1 ≤ L) (hbig : 2 * (M * Hp + M * Hn + A * B + A + L + 2 * B + 2) < 2 ^ C.Wd) :
    Hs C axisS a 60 (fun b => b.env vLo = (M * Hp + A + A * B - (M * Hn + L)) / A ∧
      b.env vLen = min ((M * Hp + (L - 1) + A * B + A - M * Hn) / A) (2 * B + 1) -
        (M * Hp + A + A * B - (M * Hn + L)) / A ∧ Same a b ∧ Fr a b axisT ∧ Cst b) := by
  have hcT : vZ ∉ axisT ∧ v1 ∉ axisT ∧ v2 ∉ axisT := by decide
  have h1 : M * Hp < 2 ^ C.Wd := by nlinarith
  have h2 : A * B < 2 ^ C.Wd := by nlinarith
  have h3 : M * Hn < 2 ^ C.Wd := by nlinarith
  refine Hx.hs (Hs.then (hs_mul C aM aHp xP1 a (by decide) (by decide) (by decide) (by rw [hM, hHp]; exact h1))
    (fun b0 hb0 n0 hn0 => ?_))
  subst hb0
  refine Hs.then (hs_mul C aA aB xP2 _ (by decide) (by decide) (by decide) (by vsimp [hA, hB]; exact h2))
    (fun b1 hb1 n1 hn1 => ?_)
  subst hb1
  refine Hs.then (hs_mul C aM aHn xP3 _ (by decide) (by decide) (by decide) (by vsimp [hM, hHn]; exact h3))
    (fun b2 hb2 n2 hn2 => ?_)
  subst hb2
  refine Hs.then (hs_copy C xX xP1 _ (by decide)) (fun b3 hb3 n3 hn3 => ?_)
  subst hb3
  refine Hs.then (hs_add C xX aA _ (by decide) (by vsimp [hM, hHp, hA]; omega)) (fun b4 hb4 n4 hn4 => ?_)
  subst hb4
  refine Hs.then (hs_add C xX xP2 _ (by decide) (by vsimp [hM, hHp, hA, hB]; omega)) (fun b5 hb5 n5 hn5 => ?_)
  subst hb5
  refine Hs.then (hs_copy C xY xP3 _ (by decide)) (fun b6 hb6 n6 hn6 => ?_)
  subst hb6
  refine Hs.then (hs_add C xY aL _ (by decide) (by vsimp [hM, hHn, hL]; omega)) (fun b7 hb7 n7 hn7 => ?_)
  subst hb7
  refine Hs.then (tsubS_spec xX xY (by decide) _) (fun b8 hb8 n8 hn8 => ?_)
  subst hb8
  refine Hs.then (hs_dm C xX aA vLo xR _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by vsimp [hA]; omega) (by vsimp [hA]; omega)) (fun b9 hb9 n9 hn9 => ?_)
  subst hb9
  refine Hs.then (hs_copy C xX xP1 _ (by decide)) (fun b10 hb10 n10 hn10 => ?_)
  subst hb10
  refine Hs.then (hs_add C xX aL _ (by decide) (by vsimp [hM, hHp, hL]; omega)) (fun b11 hb11 n11 hn11 => ?_)
  subst hb11
  refine Hs.then (hs_sub C xX v1 _ (by decide) (by vsimp [hM, hHp, hL, hc.one]; omega))
    (fun b12 hb12 n12 hn12 => ?_)
  subst hb12
  refine Hs.then (hs_add C xX xP2 _ (by decide) (by vsimp [hM, hHp, hL, hc.one, hA, hB]; omega))
    (fun b13 hb13 n13 hn13 => ?_)
  subst hb13
  refine Hs.then (hs_add C xX aA _ (by decide) (by vsimp [hM, hHp, hL, hc.one, hA, hB]; omega))
    (fun b14 hb14 n14 hn14 => ?_)
  subst hb14
  refine Hs.then (tsubS_spec xX xP3 (by decide) _) (fun b15 hb15 n15 hn15 => ?_)
  subst hb15
  refine Hs.then (hs_dm C xX aA xQ xR _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by vsimp [hA]; omega) (by vsimp [hA]; omega)) (fun b16 hb16 n16 hn16 => ?_)
  subst hb16
  refine Hs.then (hs_copy C xC aB _ (by decide)) (fun b17 hb17 n17 hn17 => ?_)
  subst hb17
  refine Hs.then (hs_shl C xC _ (by vsimp [hB]; omega)) (fun b18 hb18 n18 hn18 => ?_)
  subst hb18
  refine Hs.then (hs_inc C xC _ (by vsimp [hB]; omega)) (fun b19 hb19 n19 hn19 => ?_)
  subst hb19
  have hX2 : M * Hp + L - 1 + A * B + A = M * Hp + (L - 1) + A * B + A := by omega
  refine Hs.then (minS_spec xQ xC (by decide) (by decide) _ ⟨by vsimp [hc.z], by vsimp [hc.one], by vsimp [hc.two]⟩
    (by vsimp [hM, hHp, hA, hB, hL, hHn, hc.one]; exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)))
    (fun b20 hb20 n20 hn20 => ?_)
  subst hb20
  refine Hs.then (hs_copy C vLen xQ _ (by decide)) (fun b21 hb21 n21 hn21 => ?_)
  subst hb21
  refine Hs.last (tsubS_spec vLen vLo (by decide) _) (fun b22 hb22 n22 hn22 => ?_)
  subst hb22
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, by omega⟩
  · vsimp [hM, hHp, hA, hB, hHn, hL]
  · vsimp [hM, hHp, hA, hB, hHn, hL, hc.one]
    rw [hX2]
  · exact ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩
  · intro y hy
    have hy' : y ∉ [vLo, vLen, xP1, xP2, xP3, xX, xY, xR, xQ, xC] := hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy'
    obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10⟩ := hy'
    simp only [DS.set_env_ne _ _ n1, DS.set_env_ne _ _ n2, DS.set_env_ne _ _ n3, DS.set_env_ne _ _ n4,
      DS.set_env_ne _ _ n5, DS.set_env_ne _ _ n6, DS.set_env_ne _ _ n7, DS.set_env_ne _ _ n8, DS.set_env_ne _ _ n9,
      DS.set_env_ne _ _ n10]
  · exact ⟨by vsimp [hc.z], by vsimp [hc.one], by vsimp [hc.two]⟩

end NearQuarticWires.Reconstruct
