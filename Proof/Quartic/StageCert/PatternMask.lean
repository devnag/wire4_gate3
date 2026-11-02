import Proof.Quartic.Builder.CellCall
import Proof.Quartic.Mask.Structural
import Proof.Quartic.StageCert.IncidencePhysical

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicWires NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.FinalPass
open Finset

/-- `imp:partition` and `def:mask`, paper/paper.tex: one original pattern coordinate is its least-significant-first
base-`b+1` digit, without any finite-enumeration choice. -/
def patternSlot (P : StarParams) (index : Fin ((P.b+1)^(P.r/2)))
    (j : Fin (P.r/2)) : Fin (P.b+1) :=
  ⟨index.val/(P.b+1)^j.val%(P.b+1),Nat.mod_lt _ (Nat.succ_pos _)⟩

/-- `imp:partition` and `def:mask`, paper/paper.tex: zero digit means no error, and digit `i+1` flips coordinate `i`. -/
def decodedPattern (P : StarParams) (index : Fin ((P.b+1)^(P.r/2))) : P.Errors :=
  fun j => (optionFinEquiv P.b).symm (patternSlot P index j)

/-- `imp:partition`, paper/paper.tex: the explicit arithmetic
pattern decoder agrees exactly with the canonical original pattern order. -/
theorem decodedPattern_eq (P : StarParams) (index : Fin ((P.b+1)^(P.r/2))) :
    decodedPattern P index=(errorsEquiv P).symm index := by
  funext j
  apply (optionFinEquiv P.b).injective
  simp only [decodedPattern,Equiv.apply_symm_apply]
  unfold errorsEquiv
  change patternSlot P index j=(optionFinEquiv P.b)
    ((optionFinEquiv P.b).symm ((finFunctionFinEquiv.symm index) j))
  rw [Equiv.apply_symm_apply]
  rfl

/-- `def:mask`, paper/paper.tex: one side is accepted iff
all original coordinates flipped by its numeric pattern are nonheavy. -/
def patternAvoids (P : StarParams) (degree : Fin P.n→ℕ) (dstar : ℕ)
    (side : Fin (P.r/2)→Fin P.r) (index : Fin ((P.b+1)^(P.r/2))) : Bool :=
  (List.finRange (P.r/2)).all fun j => match decodedPattern P index j with
    | none => true
    | some i => decide (degree (P.blockCoord (side j) i)<dstar)

/-- `def:mask`, paper/paper.tex: the finite pattern test is
exactly the original heavy-coordinate disjointness predicate. -/
theorem patternAvoids_eq_true (P : StarParams) (degree : Fin P.n→ℕ) (dstar : ℕ)
    (side : Fin (P.r/2)→Fin P.r) (index : Fin ((P.b+1)^(P.r/2))) :
    patternAvoids P degree dstar side index=true ↔
      Disjoint (P.flipSet side ((errorsEquiv P).symm index)) (Mask.heavyCoordinates degree dstar) := by
  rw [patternAvoids,List.all_eq_true]
  simp only [List.mem_finRange,true_implies]
  rw [Finset.disjoint_left]
  constructor
  · intro h x hx hheavy
    obtain ⟨j,i,hji,rfl⟩ := (P.mem_flipSet _ _ _).mp hx
    have hj := h j
    rw [decodedPattern_eq,hji] at hj
    have hl : degree (P.blockCoord (side j) i)<dstar := by simpa using hj
    have hg : dstar≤degree (P.blockCoord (side j) i) := by simpa [Mask.heavyCoordinates] using hheavy
    omega
  · intro h j
    cases he : decodedPattern P index j with
    | none => rfl
    | some i =>
      have hm : P.blockCoord (side j) i∈P.flipSet side ((errorsEquiv P).symm index) := by
        apply (P.mem_flipSet _ _ _).mpr
        exact ⟨j,i,by rw [←decodedPattern_eq]; exact he,rfl⟩
      have hn := h hm
      have hl : degree (P.blockCoord (side j) i)<dstar := by
        by_contra hc
        exact hn (by simp [Mask.heavyCoordinates,Nat.le_of_not_gt hc])
      simpa using hl

/-- `def:mask`, paper/paper.tex: the actual pair mask is
the disjunction of two independently computed numeric side flags. -/
theorem structuralMask_eq_patternAvoids (P : StarParams) (degree : Fin P.n→ℕ) (dstar : ℕ)
    (u v : Fin ((P.b+1)^(P.r/2))) :
    Mask.structuralMask (P.flipSet P.leftBlock) (P.flipSet P.rightBlock)
      (Mask.heavyCoordinates degree dstar) ((errorsEquiv P).symm u) ((errorsEquiv P).symm v)=
        (patternAvoids P degree dstar P.leftBlock u || patternAvoids P degree dstar P.rightBlock v) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Mask.structuralMask,decide_eq_true_eq,Bool.or_eq_true,patternAvoids_eq_true]

end NearQuarticWires.StageCert
