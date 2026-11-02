import Proof.Quartic.Reconstruct.SystemLink

/-!
# Writing one system

Paper: Step 3 of `sec:algorithm`, paper/paper.tex.

From the part (in `gS`) and the two coordinate intervals of the box (in `pLo0 … pB1`), and with the rows of the system
on the input, `itemEmitS` writes `frame tag ++ frame sysWord` at depth `1` (`itemEmitS_spec`): the tag
`intWord (±2) ++ natWord idx₀` (`TagProgram.tagS_spec`), the points (`PointsProgram.pointsS_spec`) and the rows copied
from the input (`CopyProgram.rowsCopyS_spec`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces (listWord)

variable {C : Ctx}

/-- Write the framed tag and the framed word of one system at depth `1`. -/
def itemEmitS : St VV MM :=
  .seq (tagS 2) (.seq (putD 1 false) (.seq (pointsS 2) (.seq (rowsCopyS 2) (putD 1 false))))

/-- The variables written by `itemEmitS`. -/
def itemEmitT : List (Fin VV) := [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, vJ, gU, gV, pI, pJ, pX, cN, cK]

/-- The word of one written system. -/
def itemWord (s : Bool) (lo0 len0 B0 lo1 len1 B1 : ℕ) (rows : List (ℕ × List ℕ × ℕ)) : List Bool :=
  RepairOrdinary.frame (NearCubicGates.Close.Interfaces.intWord (coefOf s) ++
      natWord (zeroIndex lo0 len0 B0 lo1 len1 B1)) ++
    RepairOrdinary.frame (natWord (len0 * len1) ++ pointsWord lo0 len0 B0 lo1 len1 B1 ++ listWord rowWord rows)

/-- The cost of writing one system. -/
def itemEmitCost (W ℓ len0 len1 rows : ℕ) : ℕ :=
  3 * emitNatDCost 2 W + pointsCost 2 ℓ len0 len1 + (5 * rows + 1) * (copyCost 2 ℓ + 4) + 100

theorem itemEmitS_spec (a : DS VV MM) (hc : Cst a) (hW : 3 ≤ C.Wd) (s : Bool) (hs : a.env gS = if s then 1 else 0)
    (ℓ : ℕ) (rows : List (ℕ × List ℕ × ℕ)) (rest : List Bool)
    (hin : C.inp.drop a.ip = listWord rowWord rows ++ rest) (h2 : ∀ row ∈ rows, row.2.1.length = 2)
    (hbig : (a.env pLo0 + a.env pLen0 + a.env pB0 + a.env pLo1 + a.env pLen1 + a.env pB1 + 1) ^ 2 < 2 ^ C.Wd)
    (hfit0 : natBitLength (a.env pLo0 + a.env pLen0 + a.env pB0) ≤ ℓ)
    (hfit1 : natBitLength (a.env pLo1 + a.env pLen1 + a.env pB1) ≤ ℓ) (hℓ : ℓ + 2 ≤ C.Wd)
    (hprod : natBitLength (a.env pLen0 * a.env pLen1) ≤ ℓ)
    (hrows : ∀ v ∈ rows.length :: rows.flatMap rowNats, natBitLength v ≤ ℓ) (hNW : 5 * rows.length < 2 ^ C.Wd) :
    Hs C itemEmitS a (itemEmitCost C.Wd ℓ (a.env pLen0) (a.env pLen1) rows.length)
      (fun b => Moved a b (listWord rowWord rows).length (marksD 1 (itemWord s (a.env pLo0) (a.env pLen0)
        (a.env pB0) (a.env pLo1) (a.env pLen1) (a.env pB1) rows)) itemEmitT ∧ Cst b) := by
  set S := a.env pLo0 + a.env pLen0 + a.env pB0 + a.env pLo1 + a.env pLen1 + a.env pB1 + 1 with hS
  have hsq : S ≤ S ^ 2 := Nat.le_self_pow (by norm_num) _
  have hWl : C.Wd < 2 ^ C.Wd := Nat.lt_two_pow_self
  have htT : ∀ y ∈ tagT, y ∈ itemEmitT := by decide
  have hpT : ∀ y ∈ pointsT, y ∈ itemEmitT := by decide
  have hrT : ∀ y ∈ rowsCopyT, y ∈ itemEmitT := by decide
  have hjT : ∀ y ∈ [vJ], y ∈ itemEmitT := by decide
  have hin6 : ∀ y ∈ [pLo0, pLen0, pB0, pLo1, pLen1, pB1], y ∉ itemEmitT := by decide
  refine Hx.hs (Hs.then (tagS_spec 2 a hc hW s hs hbig) (fun b1 ⟨w1, c1⟩ n1 hn1 => ?_))
  refine Hs.then (putD_spec 1 false b1) (fun b2 w2 n2 hn2 => ?_)
  have w12 := (w1.weaken htT).trans (w2.weaken hjT)
  have kv : ∀ y ∈ [pLo0, pLen0, pB0, pLo1, pLen1, pB1], b2.env y = a.env y := fun y hy => w12.fr y (hin6 y hy)
  have c2 : Cst b2 := w2.cst c1 (by decide)
  have e0 := kv pLo0 (by simp)
  have e1 := kv pLen0 (by simp)
  have e2 := kv pB0 (by simp)
  have e3 := kv pLo1 (by simp)
  have e4 := kv pLen1 (by simp)
  have e5 := kv pB1 (by simp)
  have hpl : a.env pLen0 * a.env pLen1 ≤ S ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul (by omega) (by omega)
  refine Hs.then (pointsS_spec 2 b2 c2 hW ℓ (by rw [e0, e1, e2]; exact hfit0) (by rw [e3, e4, e5]; exact hfit1)
    (by omega) (by rw [e0, e1]; omega) (by rw [e3, e4]; omega) (by rw [e1, e4]; omega)
    (by rw [e1, e4]; omega)) (fun b3 ⟨w3, c3⟩ n3 hn3 => ?_)
  simp only [e0, e1, e2, e3, e4, e5] at w3 hn3
  have hin3 : C.inp.drop b3.ip = listWord rowWord rows ++ rest := by
    rw [w3.ip, w2.ip, w1.ip]; exact hin
  refine Hs.then (rowsCopyS_spec 2 ℓ b3 c3 rows rest hin3 h2 hrows hℓ hNW) (fun b4 ⟨w4, c4⟩ n4 hn4 => ?_)
  refine Hs.last (putD_spec 1 false b4) (fun b5 w5 n5 hn5 => ?_)
  refine ⟨⟨?_, w5.cst c4 (by decide)⟩, ?_⟩
  · have hm := (((Moved.of_wrote w12).trans (Moved.of_wrote (w3.weaken hpT))).trans (w4.weaken hrT)).trans
      (Moved.of_wrote (w5.weaken hjT))
    unfold itemWord
    rw [marksD_append, marksD_frame, marksD_frame]
    simp only [Nat.zero_add, Nat.add_zero, List.append_assoc, marksD_append] at hm ⊢
    exact hm
  · unfold itemEmitCost
    have : (2 : ℕ) * 2 ^ 1 + 1 = 5 := by norm_num
    simp only [this] at hn2 hn5
    omega

end NearQuarticWires.Reconstruct
