import Proof.Quartic.Program.Stages
import Proof.Quartic.Machine.Enumeration

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open Finset
open NearQuarticWires
open NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces

/-- `eq:testX`–`eq:testPhi`, paper/paper.tex: a signed moment
and the nonnegative natural threshold in its literal strict test. -/
abbrev MomentRecord := ℤ × ℕ

/-- `sec:algorithm`, paper/paper.tex: exact signed record encoding. -/
def momentRecordWord (r : MomentRecord) : List Bool := NearCubicGates.Close.Interfaces.intWord r.1 ++ natWord r.2

/-- `sec:cycle`, paper/paper.tex: all 256 sign patterns in
binary order, independently of every call and column. -/
def signPatterns : List (Cycle.SignPattern 4) :=
  List.ofFn fun a : Fin (2^8) => fun l : Fin 8 => a.val.testBit l.val

/-- `sec:cycle`, paper/paper.tex: the binary enumeration
contains every sign pattern. -/
theorem signPatterns_complete (σ : Cycle.SignPattern 4) : σ ∈ signPatterns := by
  apply List.mem_ofFn.mpr
  refine ⟨⟨NearCubicWires.WireExponent3_5.Sampler.ofBits σ,
    NearCubicWires.WireExponent3_5.Sampler.ofVec_lt _⟩, ?_⟩
  funext l
  exact NearCubicWires.WireExponent3_5.Sampler.testBit_ofBits σ l l.isLt

/-- `eq:testX`, paper/paper.tex: the complete population record. -/
noncomputable def populationRecord {N J : ℕ} (k : ℕ) (D : Walks.WalkData N 4 J) : MomentRecord :=
  (Walks.momentSum k (fun x : Walks.StructuralPoint D.structural => (D.X x.val : ℤ)),
    (D.Xmax+1)^(2*k))

/-- `eq:testE`, paper/paper.tex: one digit record, with its exact
polynomial mask before certification. -/
noncomputable def digitRecord {N J : ℕ} (k : ℕ) (D : Walks.WalkData N 4 J)
    (j : Fin 2) (σ : Cycle.SignPattern 4) (r : Fin (J+1)) : MomentRecord :=
  (Walks.maskedMoment (4*k)
    (fun w : Walks.StructuralWalk (by norm_num) D.structural =>
      Walks.walkMaskPoly (by norm_num) D.structural D.tau D.Xmax D.X w.val)
    (fun w => D.E j σ w.val r), D.hE^(2*(4*k)))

/-- `eq:testPhi`, paper/paper.tex: one final-error record. -/
noncomputable def finalRecord {N J : ℕ} (k : ℕ) (D : Walks.WalkData N 4 J)
    (j : Fin 2) (σ : Cycle.SignPattern 4) : MomentRecord :=
  (Walks.maskedMoment (4*k)
    (fun w : Walks.StructuralWalk (by norm_num) D.structural =>
      Walks.walkMaskPoly (by norm_num) D.structural D.tau D.Xmax D.X w.val)
    (fun w => D.phi (by norm_num) j σ w.val), D.Lambda^(2*(4*k)))

/-- `sec:algorithm`, paper/paper.tex: column-major strict tests,
with the population test first and only the sign patterns required by κ. -/
noncomputable def columnRecords {N J : ℕ} (k : ℕ) (D : Walks.WalkData N 4 J) : List MomentRecord := by
  classical
  exact populationRecord k D :: (List.finRange 2).flatMap fun j =>
    if j ∈ D.circuits then signPatterns.flatMap (fun σ =>
      if Cycle.kappa 4 σ ≠ 0 then
        (List.ofFn (digitRecord k D j σ)) ++ [finalRecord k D j σ]
      else []) else []

/-- `eq:testX`–`eq:testPhi`, paper/paper.tex: passing the
finite record stream is exactly the mathematical column certificate. -/
theorem columnRecords_pass_iff {N J : ℕ} (k : ℕ) (D : Walks.WalkData N 4 J) :
    (∀ r ∈ columnRecords k D, r.1 < (r.2 : ℤ)) ↔
      Walks.ColumnCertificate (by norm_num) k D := by
  classical
  simp only [columnRecords, List.mem_cons, List.mem_flatMap, List.mem_finRange,
    true_and]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · have hp := h (populationRecord k D) (Or.inl rfl)
      simpa [populationRecord] using hp
    · intro j hj σ hσ r
      have hr : digitRecord k D j σ r ∈
          List.ofFn (digitRecord k D j σ) ++ [finalRecord k D j σ] := by
        apply List.mem_append_left
        exact List.mem_ofFn.mpr ⟨r, rfl⟩
      have hp := h (digitRecord k D j σ r)
        (Or.inr ⟨j, by rw [if_pos hj]; exact List.mem_flatMap.mpr ⟨σ, signPatterns_complete σ, by simpa [hσ] using hr⟩⟩)
      simpa [digitRecord] using hp
    · intro j hj σ hσ
      have hr : finalRecord k D j σ ∈
          List.ofFn (digitRecord k D j σ) ++ [finalRecord k D j σ] := by simp
      have hp := h (finalRecord k D j σ)
        (Or.inr ⟨j, by rw [if_pos hj]; exact List.mem_flatMap.mpr ⟨σ, signPatterns_complete σ, by simp [hσ]⟩⟩)
      simpa [finalRecord] using hp
  · intro h r hr
    rcases hr with rfl | ⟨j, hj⟩
    · simpa [populationRecord] using h.population
    · by_cases hc : j ∈ D.circuits
      · rw [if_pos hc] at hj
        obtain ⟨σ, _, hs⟩ := List.mem_flatMap.mp hj
        by_cases hk : Cycle.kappa 4 σ ≠ 0
        · rw [if_pos hk] at hs
          rcases List.mem_append.mp hs with he | hf
          · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
            simpa [digitRecord] using h.digits j hc σ hk i
          · have : r = finalRecord k D j σ := by simpa using hf
            subst r
            simpa [finalRecord] using h.finalError j hc σ hk
        · simp [hk] at hs
      · simp [hc] at hj

end NearQuarticWires.StageCert
