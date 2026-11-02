import Proof.Quartic.StageCert.PatternLoop
import Proof.Quartic.StageCert.PatternMask

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicWires NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.FinalPass
open NearCubicGates.Close.Interfaces

/-- `def:mask`, paper/paper.tex: the accumulated numeric
side flag is exactly the conjunction over its original block slots. -/
theorem Incidence.prefixNonheavy_iff (c : Call) (cut b offset code count : ℕ) :
    Incidence.prefixNonheavy c cut b offset code count ↔
      ∀j<count,Incidence.digitNonheavy c cut b (offset+j) (code/(b+1)^j%(b+1)) := by
  induction count with
  | zero => simp [Incidence.prefixNonheavy]
  | succ n ih =>
    rw [Incidence.prefixNonheavy,ih]
    constructor
    · rintro ⟨h,hLast⟩ j hj
      by_cases hlt : j<n
      · exact h j hlt
      · have : j=n := by omega
        simpa only [this] using hLast
    · intro h
      exact ⟨fun j hj => h j (by omega),h n (by omega)⟩

/-- `def:mask`, paper/paper.tex: one numeric radix digit
has exactly the same nonheavy test as its canonical error-coordinate option. -/
theorem patternSlot_nonheavy (P : StarParams) (c : Call) (cut offset : ℕ)
    (side : Fin (P.r/2)→Fin P.r)
    (hside : ∀j,(side j).val=offset+j.val)
    (index : Fin ((P.b+1)^(P.r/2))) (j : Fin (P.r/2)) :
    (match decodedPattern P index j with
      | none => true
      | some i => decide (Incidence.sourceDegree c (P.blockCoord (side j) i).val<cut))=
    decide (Incidence.digitNonheavy c cut P.b (offset+j.val)
      (index.val/(P.b+1)^j.val%(P.b+1))) := by
  change (match (if h : (patternSlot P index j).val=0 then none else
      some (⟨(patternSlot P index j).val-1,by
        have := (patternSlot P index j).isLt
        omega⟩ : Fin P.b)) with
    | none => true
    | some i => decide (Incidence.sourceDegree c (P.blockCoord (side j) i).val<cut))=_
  by_cases hz : index.val/(P.b+1)^j.val%(P.b+1)=0
  · simp [patternSlot,hz,Incidence.digitNonheavy]
  · simp [patternSlot,hz,Incidence.digitNonheavy,StarParams.blockCoord,hside]

/-- `def:mask`, paper/paper.tex: the physical numeric
side-loop flag agrees with the canonical error-pattern structural test. -/
theorem patternAvoids_eq_numeric (P : StarParams) (c : Call) (cut offset : ℕ)
    (side : Fin (P.r/2)→Fin P.r)
    (hside : ∀j,(side j).val=offset+j.val)
    (index : Fin ((P.b+1)^(P.r/2))) :
    patternAvoids P (fun i=>Incidence.sourceDegree c i.val) cut side index=
      decide (Incidence.prefixNonheavy c cut P.b offset index.val (P.r/2)) := by
  apply Bool.eq_iff_iff.mpr
  rw [patternAvoids,List.all_eq_true,decide_eq_true_eq,Incidence.prefixNonheavy_iff]
  simp only [List.mem_finRange,true_implies]
  constructor
  · intro h j hj
    have hh := h ⟨j,hj⟩
    exact of_decide_eq_true
      ((patternSlot_nonheavy P c cut offset side hside index ⟨j,hj⟩).symm.trans hh)
  · intro h j
    exact (patternSlot_nonheavy P c cut offset side hside index j).trans
      (decide_eq_true (h j.val j.isLt))

end NearQuarticWires.StageCert
