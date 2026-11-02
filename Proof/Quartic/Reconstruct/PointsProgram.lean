import Proof.Quartic.Reconstruct.EmitInt
import Proof.Quartic.Reconstruct.AxisProgram

/-!
# The points of a box in the cell language

Paper: Step 3 of `sec:algorithm`, paper/paper.tex (the unknowns of a system are the points of `Bx(δ)`).

The two coordinate intervals of the box are given by their shifted starts `lo'_j`, their numbers of points `len_j`
and their shifts `B_j` (`BoxArith.boxAxisOf_eq`). `pointsS d` writes, at depth `d` of marks, the number of points
`len_1 len_2` and then, for every point `(y_1, y_2)` in the order of `boxPoints` (first coordinate outermost), its
word `listWord intWord [y_1, y_2]` (`pointsS_spec`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells

variable {C : Ctx}

/-- `lo'_1`. -/
def pLo0 : Fin VV := ⟨41, by decide⟩
/-- `len_1`. -/
def pLen0 : Fin VV := ⟨42, by decide⟩
/-- `B_1`. -/
def pB0 : Fin VV := ⟨43, by decide⟩
/-- `lo'_2`. -/
def pLo1 : Fin VV := ⟨44, by decide⟩
/-- `len_2`. -/
def pLen1 : Fin VV := ⟨45, by decide⟩
/-- `B_2`. -/
def pB1 : Fin VV := ⟨46, by decide⟩
/-- The counter of the first coordinate. -/
def pI : Fin VV := ⟨47, by decide⟩
/-- The counter of the second coordinate. -/
def pJ : Fin VV := ⟨48, by decide⟩
/-- A shifted coordinate. -/
def pX : Fin VV := ⟨49, by decide⟩

/-- The word of the point `(lo'_1 + i - B_1, lo'_2 + j - B_2)`. -/
def pointWord (lo0 B0 lo1 B1 i j : ℕ) : List Bool :=
  natWord 2 ++ NearCubicGates.Close.Interfaces.intWord (((lo0 + i : ℕ) : ℤ) - B0) ++
    NearCubicGates.Close.Interfaces.intWord (((lo1 + j : ℕ) : ℤ) - B1)

/-- The words of the points `j < len_2` of the row `i`. -/
def rowPointsWord (lo0 B0 lo1 len1 B1 i : ℕ) : List Bool :=
  (List.range len1).flatMap (pointWord lo0 B0 lo1 B1 i)

/-- The words of all points, the first coordinate outermost. -/
def pointsWord (lo0 len0 B0 lo1 len1 B1 : ℕ) : List Bool :=
  (List.range len0).flatMap (rowPointsWord lo0 B0 lo1 len1 B1)

/-- One point. -/
def pointS (d : ℕ) : St VV MM :=
  .seq (.op (.zero t3)) (.seq (.op (.inc t3)) (.seq (.op (.inc t3)) (.seq (emitNatD d)
    (.seq (.op (.copy pX pLo0)) (.seq (.op (.add pX pI)) (.seq (emitShiftD d pX pB0)
      (.seq (.op (.copy pX pLo1)) (.seq (.op (.add pX pJ)) (emitShiftD d pX pB1)))))))))

/-- The variables written by `pointS`. -/
def pointT : List (Fin VV) := pX :: emitShiftT

/-- The cost of one point on values of bit length at most `ℓ`. -/
def pointCost (d ℓ : ℕ) : ℕ := emitNatDCost d 2 + 2 * emitShiftCost d ℓ + 20

theorem emitShiftCost_mono (d : ℕ) {x y : ℕ} (h : x ≤ y) : emitShiftCost d x ≤ emitShiftCost d y := by
  unfold emitShiftCost emitNatDCost
  have := Nat.mul_le_mul_left (4 * 2 ^ d + 20) (show x + 3 ≤ y + 3 by omega)
  omega

theorem pointS_spec (d : ℕ) (a : DS VV MM) (hc : Cst a) (hW : 3 ≤ C.Wd) (ℓ : ℕ)
    (hfit0 : natBitLength (a.env pLo0 + a.env pI + a.env pB0) ≤ ℓ)
    (hfit1 : natBitLength (a.env pLo1 + a.env pJ + a.env pB1) ≤ ℓ) (hℓ : ℓ + 2 < 2 ^ C.Wd)
    (hv0 : a.env pLo0 + a.env pI < 2 ^ C.Wd) (hv1 : a.env pLo1 + a.env pJ < 2 ^ C.Wd) :
    Hs C (pointS d) a (pointCost d ℓ)
      (fun b => Wrote a b (marksD d (pointWord (a.env pLo0) (a.env pB0) (a.env pLo1) (a.env pB1) (a.env pI)
        (a.env pJ))) pointT ∧ Cst b) := by
  have hst : ∀ y ∈ emitShiftT, y ∈ pointT := fun y hy => List.mem_cons_of_mem _ hy
  have hnt : ∀ y ∈ emitNatDT, y ∈ pointT := fun y hy => hst y (List.mem_cons_of_mem _ hy)
  have h3 : t3 ∈ pointT := by decide
  have hX : pX ∈ pointT := by decide
  have hcT : vZ ∉ pointT ∧ v1 ∉ pointT ∧ v2 ∉ pointT := by decide
  have h2W : 8 ≤ 2 ^ C.Wd := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) hW
  have hW2 : 2 ≤ C.Wd := by omega
  -- the frame facts for the inputs
  have keep : ∀ (b c : DS VV MM) (T : List (Fin VV)), Fr b c T →
      (∀ y ∈ [pLo0, pB0, pLo1, pB1, pI, pJ], y ∉ T) →
      c.env pLo0 = b.env pLo0 ∧ c.env pB0 = b.env pB0 ∧ c.env pLo1 = b.env pLo1 ∧ c.env pB1 = b.env pB1 ∧
        c.env pI = b.env pI ∧ c.env pJ = b.env pJ := by
    intro b c T h hT
    exact ⟨h _ (hT _ (by simp)), h _ (hT _ (by simp)), h _ (hT _ (by simp)), h _ (hT _ (by simp)),
      h _ (hT _ (by simp)), h _ (hT _ (by simp))⟩
  have hn6 : ∀ y ∈ [pLo0, pB0, pLo1, pB1, pI, pJ], y ∉ emitNatDT := by decide
  have hs6 : ∀ y ∈ [pLo0, pB0, pLo1, pB1, pI, pJ], y ∉ emitShiftT := by decide
  refine Hx.hs (Hs.then (hs_zero C t3 a) (fun b0 hb0 n0 hn0 => ?_))
  subst hb0
  refine Hs.then (hs_inc C t3 _ (by vsimp []; omega)) (fun b1 hb1 n1 hn1 => ?_)
  subst hb1
  refine Hs.then (hs_inc C t3 _ (by vsimp []; omega)) (fun b2 hb2 n2 hn2 => ?_)
  subst hb2
  set a2 := ((a.set t3 0).set t3 ((a.set t3 0).env t3 + 1)).set t3
    (((a.set t3 0).set t3 ((a.set t3 0).env t3 + 1)).env t3 + 1) with ha2
  have c2 : Cst a2 := ⟨by vsimp [ha2, hc.z], by vsimp [ha2, hc.one], by vsimp [ha2, hc.two]⟩
  have e2 : a2.env t3 = 2 := by vsimp [ha2]
  have w2 : Wrote a a2 [] pointT := (((Wrote.refl a pointT).set _ h3).set _ h3).set _ h3
  have k2 := keep a a2 pointT w2.fr (by decide)
  have hnb2 : natBitLength 2 = 2 := by simp [natBitLength]; decide
  refine Hs.then (emitNatD_spec d a2 c2 hW2 (by rw [e2, hnb2]; omega)) (fun b3 hb3 n3 hn3 => ?_)
  obtain ⟨w3, c3⟩ := hb3
  rw [e2] at w3 hn3
  have k3 := keep a2 b3 emitNatDT w3.fr hn6
  refine Hs.then (hs_copy C pX pLo0 b3 (by decide)) (fun b4 hb4 n4 hn4 => ?_)
  subst hb4
  refine Hs.then (hs_add C pX pI _ (by decide) (by vsimp [k3.1, k3.2.2.2.2.1, k2.1, k2.2.2.2.2.1]; exact hv0))
    (fun b5 hb5 n5 hn5 => ?_)
  subst hb5
  set a5 := (b3.set pX (b3.env pLo0)).set pX ((b3.set pX (b3.env pLo0)).env pX + (b3.set pX (b3.env pLo0)).env pI)
    with ha5
  have c5 : Cst a5 := ⟨by vsimp [ha5, c3.z], by vsimp [ha5, c3.one], by vsimp [ha5, c3.two]⟩
  have e5 : a5.env pX = a.env pLo0 + a.env pI := by vsimp [ha5, k3.1, k3.2.2.2.2.1, k2.1, k2.2.2.2.2.1]
  have e5B : a5.env pB0 = a.env pB0 := by vsimp [ha5, k3.2.1, k2.2.1]
  refine Hs.then (emitShiftD_spec d pX pB0 (by decide) (by decide) (by decide) a5 c5 hW2
    (by rw [e5, e5B]; have := natBitLength_mono (show a.env pLo0 + a.env pI + a.env pB0 ≤ _ from le_rfl); omega))
    (fun b6 hb6 n6 hn6 => ?_)
  obtain ⟨w6, c6⟩ := hb6
  rw [e5, e5B] at w6 hn6
  have k6 := keep a5 b6 emitShiftT w6.fr hs6
  have k5 : a5.env pLo1 = a.env pLo1 ∧ a5.env pB1 = a.env pB1 ∧ a5.env pJ = a.env pJ := by
    refine ⟨?_, ?_, ?_⟩ <;> vsimp [ha5, k3.2.2.1, k3.2.2.2.1, k3.2.2.2.2.2, k2.2.2.1, k2.2.2.2.1, k2.2.2.2.2.2]
  refine Hs.then (hs_copy C pX pLo1 b6 (by decide)) (fun b7 hb7 n7 hn7 => ?_)
  subst hb7
  refine Hs.then (hs_add C pX pJ _ (by decide) (by
      vsimp [k6.2.2.1, k6.2.2.2.2.2, k5.1, k5.2.2]; exact hv1)) (fun b8 hb8 n8 hn8 => ?_)
  subst hb8
  set a8 := (b6.set pX (b6.env pLo1)).set pX ((b6.set pX (b6.env pLo1)).env pX + (b6.set pX (b6.env pLo1)).env pJ)
    with ha8
  have c8 : Cst a8 := ⟨by vsimp [ha8, c6.z], by vsimp [ha8, c6.one], by vsimp [ha8, c6.two]⟩
  have e8 : a8.env pX = a.env pLo1 + a.env pJ := by vsimp [ha8, k6.2.2.1, k6.2.2.2.2.2, k5.1, k5.2.2]
  have e8B : a8.env pB1 = a.env pB1 := by vsimp [ha8, k6.2.2.2.1, k5.2.1]
  refine Hs.last (emitShiftD_spec d pX pB1 (by decide) (by decide) (by decide) a8 c8 hW2
    (by rw [e8, e8B]; omega)) (fun b9 hb9 n9 hn9 => ?_)
  obtain ⟨w9, c9⟩ := hb9
  rw [e8, e8B] at w9 hn9
  refine ⟨⟨?_, c9⟩, ?_⟩
  · have hw := (((w2.trans (w3.weaken hnt)).trans (((Wrote.refl b3 pointT).set _ hX).set _ hX)).trans
      (w6.weaken hst)).trans ((((Wrote.refl b6 pointT).set _ hX).set _ hX).trans (w9.weaken hst))
    unfold pointWord
    rw [marksD_append, marksD_append]
    push_cast
    simpa using hw
  · have m1 := emitShiftCost_mono d hfit0
    have m2 := emitShiftCost_mono d hfit1
    rw [hnb2] at hn3
    unfold pointCost
    omega

/-! ## The rows and the box -/

/-- The points of row `i` (in `pI`): `j = 0, …, len_2 - 1`. -/
def rowS (d : ℕ) : St VV MM :=
  .seq (.op (.zero pJ)) (.loop (.lt pJ pLen1) (.seq (pointS d) (.op (.inc pJ))))

/-- The variables written by `rowS`. -/
def rowT : List (Fin VV) := pJ :: pointT

theorem rowS_spec (d : ℕ) (a : DS VV MM) (hc : Cst a) (hW : 3 ≤ C.Wd) (ℓ : ℕ)
    (hfit0 : natBitLength (a.env pLo0 + a.env pI + a.env pB0) ≤ ℓ)
    (hfit1 : natBitLength (a.env pLo1 + a.env pLen1 + a.env pB1) ≤ ℓ) (hℓ : ℓ + 2 < 2 ^ C.Wd)
    (hv0 : a.env pLo0 + a.env pI < 2 ^ C.Wd) (hv1 : a.env pLo1 + a.env pLen1 < 2 ^ C.Wd) :
    Hs C (rowS d) a (a.env pLen1 * (pointCost d ℓ + 4) + 4)
      (fun b => Wrote a b (marksD d (rowPointsWord (a.env pLo0) (a.env pB0) (a.env pLo1) (a.env pLen1)
        (a.env pB1) (a.env pI))) rowT ∧ Cst b) := by
  set N := a.env pLen1 with hN
  have hpr : ∀ y ∈ pointT, y ∈ rowT := fun y hy => List.mem_cons_of_mem _ hy
  have hJ : pJ ∈ rowT := by decide
  have hcT : vZ ∉ rowT ∧ v1 ∉ rowT ∧ v2 ∉ rowT := by decide
  have hin : ∀ y ∈ [pLo0, pB0, pLo1, pB1, pI, pLen1], y ∉ rowT := by decide
  let I : ℕ → DS VV MM → Prop := fun k b => b.env pJ = k ∧
    Wrote a b (marksD d ((List.range k).flatMap (pointWord (a.env pLo0) (a.env pB0) (a.env pLo1) (a.env pB1)
      (a.env pI)))) rowT ∧ Cst b
  have keep : ∀ b, Fr a b rowT → b.env pLo0 = a.env pLo0 ∧ b.env pB0 = a.env pB0 ∧ b.env pLo1 = a.env pLo1 ∧
      b.env pB1 = a.env pB1 ∧ b.env pI = a.env pI ∧ b.env pLen1 = a.env pLen1 := fun b h =>
    ⟨h _ (hin _ (by simp)), h _ (hin _ (by simp)), h _ (hin _ (by simp)), h _ (hin _ (by simp)),
      h _ (hin _ (by simp)), h _ (hin _ (by simp))⟩
  have loop : ∀ b, I 0 b → Hs C (.loop (.lt pJ pLen1) (.seq (pointS d) (.op (.inc pJ)))) b
      (N * ((pointCost d ℓ + 2) + 2) + 2) (I N) := by
    refine Hs.loopN (c := .lt pJ pLen1) (show pJ ≠ pLen1 by decide) I N (pointCost d ℓ + 2) ?_ ?_
    · intro k hk b ⟨h1, h2, h3⟩
      obtain ⟨k1, k2, k3, k4, k5, k6⟩ := keep b h2.fr
      refine ⟨by simp only [Cnd.eval, h1, k6, decide_eq_true_eq]; exact hk, ?_⟩
      refine Hs.seq (t1 := pointCost d ℓ) (t2 := 1) (pointS_spec d b h3 hW ℓ (by rw [k1, k5, k2]; exact hfit0)
        (by rw [k3, h1, k4]; exact (natBitLength_mono (by omega)).trans hfit1) hℓ (by rw [k1, k5]; exact hv0)
        (by rw [k3, h1]; omega)) (fun e ⟨we, ce⟩ => ?_)
      have eJ : e.env pJ = k := by rw [we.fr pJ (by decide), h1]
      refine Hs.mono (hs_inc C pJ e (by rw [eJ]; omega)) le_rfl ?_
      rintro f rfl
      refine ⟨by vsimp [eJ], ?_, ⟨by vsimp [ce.z], by vsimp [ce.one], by vsimp [ce.two]⟩⟩
      have hw := (h2.trans (we.weaken hpr)).set (x := pJ) (e.env pJ + 1) hJ
      rw [k1, k2, k3, k4, k5, h1] at hw
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, marksD_append]
      exact hw
    · intro b ⟨h1, h2, _⟩
      obtain ⟨_, _, _, _, _, k6⟩ := keep b h2.fr
      simp [Cnd.eval, h1, k6, hN]
  refine Hx.hs (Hs.then (hs_zero C pJ a) (fun b0 hb0 n0 hn0 => ?_))
  subst hb0
  refine Hs.last (loop _ ⟨by vsimp [], by simpa [marksD] using (Wrote.refl a rowT).set 0 hJ,
    ⟨by vsimp [hc.z], by vsimp [hc.one], by vsimp [hc.two]⟩⟩) (fun b hb n hn => ?_)
  obtain ⟨_, h2, h3⟩ := hb
  refine ⟨⟨h2, h3⟩, ?_⟩
  have : N * (pointCost d ℓ + 2 + 2) + 2 = N * (pointCost d ℓ + 4) + 2 := by ring
  omega

/-- The number of points and all points of the box, the first coordinate outermost. -/
def pointsS (d : ℕ) : St VV MM :=
  .seq (.op (.mul pLen0 pLen1 t3)) (.seq (emitNatD d) (.seq (.op (.zero pI))
    (.loop (.lt pI pLen0) (.seq (rowS d) (.op (.inc pI))))))

/-- The variables written by `pointsS`. -/
def pointsT : List (Fin VV) := pI :: rowT

/-- The cost of `pointsS`. -/
def pointsCost (d ℓ len0 len1 : ℕ) : ℕ :=
  len0 * (len1 * (pointCost d ℓ + 4) + 8) + emitNatDCost d (natBitLength (len0 * len1)) + 10

theorem pointsS_spec (d : ℕ) (a : DS VV MM) (hc : Cst a) (hW : 3 ≤ C.Wd) (ℓ : ℕ)
    (hfit0 : natBitLength (a.env pLo0 + a.env pLen0 + a.env pB0) ≤ ℓ)
    (hfit1 : natBitLength (a.env pLo1 + a.env pLen1 + a.env pB1) ≤ ℓ) (hℓ : ℓ + 2 < 2 ^ C.Wd)
    (hv0 : a.env pLo0 + a.env pLen0 < 2 ^ C.Wd) (hv1 : a.env pLo1 + a.env pLen1 < 2 ^ C.Wd)
    (hprod : a.env pLen0 * a.env pLen1 < 2 ^ C.Wd)
    (hprodl : natBitLength (a.env pLen0 * a.env pLen1) + 2 < 2 ^ C.Wd) :
    Hs C (pointsS d) a (pointsCost d ℓ (a.env pLen0) (a.env pLen1))
      (fun b => Wrote a b (marksD d (natWord (a.env pLen0 * a.env pLen1) ++ pointsWord (a.env pLo0) (a.env pLen0)
        (a.env pB0) (a.env pLo1) (a.env pLen1) (a.env pB1))) pointsT ∧ Cst b) := by
  have hrp : ∀ y ∈ rowT, y ∈ pointsT := fun y hy => List.mem_cons_of_mem _ hy
  have hnp : ∀ y ∈ emitNatDT, y ∈ pointsT := by decide
  have hI : pI ∈ pointsT := by decide
  have h3 : t3 ∈ pointsT := by decide
  have hcT : vZ ∉ pointsT ∧ v1 ∉ pointsT ∧ v2 ∉ pointsT := by decide
  have hin : ∀ y ∈ [pLo0, pB0, pLo1, pB1, pLen0, pLen1], y ∉ pointsT := by decide
  have keep : ∀ b, Fr a b pointsT → b.env pLo0 = a.env pLo0 ∧ b.env pB0 = a.env pB0 ∧
      b.env pLo1 = a.env pLo1 ∧ b.env pB1 = a.env pB1 ∧ b.env pLen0 = a.env pLen0 ∧
      b.env pLen1 = a.env pLen1 := fun b h =>
    ⟨h _ (hin _ (by simp)), h _ (hin _ (by simp)), h _ (hin _ (by simp)), h _ (hin _ (by simp)),
      h _ (hin _ (by simp)), h _ (hin _ (by simp))⟩
  have hrowc : ∀ (b : DS VV MM), Fr a b pointsT →
      b.env pLen1 * (pointCost d ℓ + 4) + 4 = a.env pLen1 * (pointCost d ℓ + 4) + 4 := fun b h => by
    rw [(keep b h).2.2.2.2.2]
  let I : ℕ → DS VV MM → Prop := fun k b => b.env pI = k ∧
    Wrote a b (marksD d (natWord (a.env pLen0 * a.env pLen1) ++ (List.range k).flatMap
      (rowPointsWord (a.env pLo0) (a.env pB0) (a.env pLo1) (a.env pLen1) (a.env pB1)))) pointsT ∧ Cst b
  have loop : ∀ b, I 0 b → Hs C (.loop (.lt pI pLen0) (.seq (rowS d) (.op (.inc pI)))) b
      (a.env pLen0 * ((a.env pLen1 * (pointCost d ℓ + 4) + 4 + 2) + 2) + 2) (I (a.env pLen0)) := by
    refine Hs.loopN (c := .lt pI pLen0) (show pI ≠ pLen0 by decide) I (a.env pLen0)
      (a.env pLen1 * (pointCost d ℓ + 4) + 4 + 2) ?_ ?_
    · intro k hk b ⟨h1, h2, h3⟩
      obtain ⟨k1, k2, k3, k4, k5, k6⟩ := keep b h2.fr
      refine ⟨by simp only [Cnd.eval, h1, k5, decide_eq_true_eq]; exact hk, ?_⟩
      have hrow := rowS_spec d b h3 hW ℓ (by rw [k1, h1, k2]; exact (natBitLength_mono (by omega)).trans hfit0)
        (by rw [k3, k6, k4]; exact hfit1) hℓ (by rw [k1, h1]; omega) (by rw [k3, k6]; exact hv1)
      rw [k6] at hrow
      refine Hs.seq (t1 := a.env pLen1 * (pointCost d ℓ + 4) + 4) (t2 := 1) hrow (fun e ⟨we, ce⟩ => ?_)
      have eI : e.env pI = k := by rw [we.fr pI (by decide), h1]
      refine Hs.mono (hs_inc C pI e (by rw [eI]; omega)) le_rfl ?_
      rintro f rfl
      refine ⟨by vsimp [eI], ?_, ⟨by vsimp [ce.z], by vsimp [ce.one], by vsimp [ce.two]⟩⟩
      have hw := (h2.trans (we.weaken hrp)).set (x := pI) (e.env pI + 1) hI
      simp only [k1, k2, k3, k4, h1] at hw
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, ← List.append_assoc, marksD_append]
      exact hw
    · intro b ⟨h1, h2, _⟩
      obtain ⟨_, _, _, _, k5, _⟩ := keep b h2.fr
      simp [Cnd.eval, h1, k5]
  refine Hx.hs (Hs.then (hs_mul C pLen0 pLen1 t3 a (by decide) (by decide) (by decide) hprod)
    (fun b0 hb0 n0 hn0 => ?_))
  subst hb0
  have c0 : Cst (a.set t3 (a.env pLen0 * a.env pLen1)) := ⟨by vsimp [hc.z], by vsimp [hc.one], by vsimp [hc.two]⟩
  have e0 : (a.set t3 (a.env pLen0 * a.env pLen1)).env t3 = a.env pLen0 * a.env pLen1 := by vsimp []
  refine Hs.then (emitNatD_spec d _ c0 (by omega) (by rw [e0]; exact hprodl)) (fun b1 hb1 n1 hn1 => ?_)
  obtain ⟨w1, c1⟩ := hb1
  rw [e0] at w1 hn1
  refine Hs.then (hs_zero C pI b1) (fun b2 hb2 n2 hn2 => ?_)
  subst hb2
  have w2 : Wrote a (b1.set pI 0) (marksD d (natWord (a.env pLen0 * a.env pLen1))) pointsT :=
    ((((Wrote.refl a pointsT).set _ h3).trans (w1.weaken hnp)).set 0 hI)
  refine Hs.last (loop _ ⟨by vsimp [], by simpa using w2,
    ⟨by vsimp [c1.z], by vsimp [c1.one], by vsimp [c1.two]⟩⟩) (fun b hb n hn => ?_)
  obtain ⟨_, h2, h3⟩ := hb
  refine ⟨⟨h2, h3⟩, ?_⟩
  unfold pointsCost
  have : a.env pLen0 * (a.env pLen1 * (pointCost d ℓ + 4) + 4 + 2 + 2) =
      a.env pLen0 * (a.env pLen1 * (pointCost d ℓ + 4) + 8) := by ring
  omega

end NearQuarticWires.Reconstruct
