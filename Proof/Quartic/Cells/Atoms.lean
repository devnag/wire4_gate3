import Proof.Quartic.Cells.Formulas
import Proof.Wire_3_5.CompilerPullback
import Proof.Wire_3_5.WalkCount

set_option autoImplicit false

namespace NearQuarticWires.Cells
open NearCubicWires NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Compiler
open NearCubicGates.Close.Tabulator

/-- `lem:print`, paper/paper.tex: edge offsets, vertex offsets, and the center. -/
abbrev OffsetRole (m : ℕ) := (Fin (2 * m) ⊕ Fin (2 * m)) ⊕ Fin 1

/-- `lem:print`, paper/paper.tex: the explicit dense indexing of the 4m+1 offsets. -/
def offsetIndex (m : ℕ) : OffsetRole m ≃ Fin (4 * m + 1) :=
  ((Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin 1))).trans finSumFinEquiv).trans
    (finCongr (by omega))

/-- `lem:print`, paper/paper.tex: row vertex of a closed-walk edge. -/
def leftSlot {m : ℕ} (hm : 0 < m) (e : Fin (2 * m)) : Fin (2 * m) :=
  if e.val % 2 = 0 then e else nextSlot (by omega) e

/-- `lem:print`, paper/paper.tex: column vertex of a closed-walk edge. -/
def rightSlot {m : ℕ} (hm : 0 < m) (e : Fin (2 * m)) : Fin (2 * m) :=
  if e.val % 2 = 0 then nextSlot (by omega) e else e

/-- `lem:print`, paper/paper.tex: the cyclic successor has opposite parity, including the wrap. -/
theorem nextSlot_parity {m : ℕ} (hm : 0 < m) (e : Fin (2 * m)) :
    (nextSlot (by omega : 0 < 2 * m) e).val % 2 = 1 - e.val % 2 := by
  by_cases h : e.val + 1 < 2 * m
  · rw [nextSlot_val _ e h]
    omega
  · have he : e.val + 1 = 2 * m := by omega
    simp only [nextSlot, he, Nat.mod_self, Nat.zero_mod]
    omega

/-- `lem:print`, paper/paper.tex: row slots are even. -/
theorem leftSlot_even {m : ℕ} (hm : 0 < m) (e : Fin (2 * m)) :
    (leftSlot hm e).val % 2 = 0 := by
  unfold leftSlot
  split
  · assumption
  · rw [nextSlot_parity hm]
    omega

/-- `lem:print`, paper/paper.tex: column slots are odd. -/
theorem rightSlot_odd {m : ℕ} (hm : 0 < m) (e : Fin (2 * m)) :
    (rightSlot hm e).val % 2 = 1 := by
  unfold rightSlot
  split
  · rw [nextSlot_parity hm]
    omega
  · omega

/-- `lem:cycle` and `lem:print`, paper/paper.tex:
the pool's slots read the actual alternating closed-walk cell. -/
theorem slots_cellOf {N m : ℕ} (hm : 0 < m) (w : Fin (2 * m) → Fin N) (e : Fin (2 * m)) :
    (w (leftSlot hm e), w (rightSlot hm e)) = cellOf (by omega) w e := by
  unfold leftSlot rightSlot cellOf
  split <;> rfl

/-- `imp:pullback` and `lem:print`, paper/paper.tex:
each role is an actual separated star coordinate map. -/
def roleCoords (P : StarParams) {m : ℕ} (hm : 0 < m) (w : Fin (2 * m) → P.Errors) :
    OffsetRole m → HalfCoords P.n (P.SideL → Bool) (P.SideR → Bool)
  | .inl (.inl e) => starCoords P (w (leftSlot hm e)) (w (rightSlot hm e)) true true
  | .inl (.inr v) => starCoords P (w v) (w v) (decide (v.val % 2 = 0)) (decide (v.val % 2 ≠ 0))
  | .inr _ => starCoords P (fun _ => none) (fun _ => none) false false

/-- `lem:print`, paper/paper.tex: all four corners reuse the same edge/vertex/center pool. -/
def cornerRole {m : ℕ} (hm : 0 < m) (e : Fin (2 * m)) : Fin 4 → OffsetRole m :=
  ![.inl (.inl e), .inl (.inr (leftSlot hm e)), .inl (.inr (rightSlot hm e)), .inr 0]

/-- `lem:print`, paper/paper.tex: literal four-corner evaluation through the bounded pool. -/
theorem cornerRole_eval (P : StarParams) {m : ℕ} (hm : 0 < m) (w : Fin (2 * m) → P.Errors)
    (g : NormalizedThresholdGate P.n) (c : BitInput P.n) (e : Fin (2 * m)) (j : Fin 4) :
    g.eval ((roleCoords P hm w (cornerRole hm e j)).point (P.leftPart c) (P.rightPart c)) =
      NearCubicWires.WireExponent3_5.Stars.corners g.eval c
        (P.errorVector P.leftBlock (w (leftSlot hm e)))
        (P.errorVector P.rightBlock (w (rightSlot hm e))) j := by
  have hL : decide ((leftSlot hm e).val % 2 = 0) = true := decide_eq_true (leftSlot_even hm e)
  have hLn : decide ((leftSlot hm e).val % 2 ≠ 0) = false := decide_eq_false (by simp [leftSlot_even hm e])
  have hR : decide ((rightSlot hm e).val % 2 = 0) = false := decide_eq_false (by simp [rightSlot_odd hm e])
  have hRn : decide ((rightSlot hm e).val % 2 ≠ 0) = true := decide_eq_true (by simp [rightSlot_odd hm e])
  fin_cases j
  · change g.eval ((starCoords P (w (leftSlot hm e)) (w (rightSlot hm e)) true true).point
      (P.leftPart c) (P.rightPart c)) = _
    rw [(starCoords_corners P _ _ c).1]
    rfl
  · change g.eval ((starCoords P (w (leftSlot hm e)) (w (leftSlot hm e))
      (decide ((leftSlot hm e).val % 2 = 0)) (decide ((leftSlot hm e).val % 2 ≠ 0))).point
      (P.leftPart c) (P.rightPart c)) = _
    rw [hL, hLn, (starCoords_corners P _ _ c).2.1]
    rfl
  · change g.eval ((starCoords P (w (rightSlot hm e)) (w (rightSlot hm e))
      (decide ((rightSlot hm e).val % 2 = 0)) (decide ((rightSlot hm e).val % 2 ≠ 0))).point
      (P.leftPart c) (P.rightPart c)) = _
    rw [hR, hRn, (starCoords_corners P _ _ c).2.2.1]
    rfl
  · change g.eval ((starCoords P (fun _ => none) (fun _ => none) false false).point
      (P.leftPart c) (P.rightPart c)) = _
    rw [(starCoords_corners P _ _ c).2.2.2]
    rfl

/-- `lem:print`, paper/paper.tex: Nw=(4m+1)G threshold atoms, with duplicate occurrences retained. -/
def atomIndex {m G : ℕ} (r : OffsetRole m) (g : Fin G) : Fin ((4 * m + 1) * G) :=
  finProdFinEquiv (offsetIndex m r, g)

/-- `lem:print`, paper/paper.tex: the actual threshold occurrence at a pool index. -/
def walkAtoms {n m G : ℕ} (gates : Fin G → NormalizedThresholdGate n)
    (i : Fin ((4 * m + 1) * G)) : NormalizedThresholdGate n := gates (finProdFinEquiv.symm i).2

/-- `lem:print`, paper/paper.tex: the actual offset at a pool index. -/
def walkCoords (P : StarParams) {m G : ℕ} (hm : 0 < m) (w : Fin (2 * m) → P.Errors)
    (i : Fin ((4 * m + 1) * G)) : HalfCoords P.n (P.SideL → Bool) (P.SideR → Bool) :=
  roleCoords P hm w ((offsetIndex m).symm (finProdFinEquiv.symm i).1)

/-- `lem:print`, paper/paper.tex: every edge residual has its four exact atoms in the shared pool. -/
theorem atomIndex_corner_eval (P : StarParams) {m G : ℕ} (hm : 0 < m)
    (w : Fin (2 * m) → P.Errors) (gates : Fin G → NormalizedThresholdGate P.n)
    (c : BitInput P.n) (e : Fin (2 * m)) (g : Fin G) (j : Fin 4) :
    (walkAtoms gates (atomIndex (cornerRole hm e j) g)).eval
      ((walkCoords P hm w (atomIndex (cornerRole hm e j) g)).point (P.leftPart c) (P.rightPart c)) =
      NearCubicWires.WireExponent3_5.Stars.corners (gates g).eval c
        (P.errorVector P.leftBlock (w (leftSlot hm e)))
        (P.errorVector P.rightBlock (w (rightSlot hm e))) j := by
  simpa only [walkAtoms, walkCoords, atomIndex, Equiv.symm_apply_apply] using
    cornerRole_eval P hm w (gates g) c e j

end NearQuarticWires.Cells
