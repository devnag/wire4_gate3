import Proof.Quartic.StageCert.RawRanges

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open Finset
open NearQuarticWires
open NearCubicWires
open NearCubicGates.Close.Interfaces

/-- `eq:testE`–`eq:testPhi`, paper/paper.tex: the complete
unconditional score range, before any strict test is assumed to pass. -/
def scoreRange (c : Call) (p : Cells.Parameters) : ℕ :=
  8*(Builder.occurrences c 0+Builder.occurrences c 1)*(1+c.n+p.M1+p.A)

/-- `lem:maskpoly`, paper/paper.tex: the complete magnitude
range of one Newton mask on an arbitrary witness-selected population. -/
def maskRange (Xmax G : ℕ) : ℕ := (Xmax+1)*2^(Xmax+G)

/-- `sec:cells`, paper/paper.tex: either circuit's occurrence
count is at most the combined count. -/
theorem occurrences_le_total (c : Call) (j : Fin 2) :
    Builder.occurrences c j ≤ Builder.occurrences c 0+Builder.occurrences c 1 := by
  fin_cases j <;> simp [Builder.occurrences, Builder.gatesOf]

variable (c : Call) {p : Cells.Parameters} (hs : Cells.ParameterRules (Builder.callInput c) p)

/-- `eq:testE`, paper/paper.tex: the combined unconditional
range applies to every digit of either original circuit. -/
theorem digit_le_scoreRange (bits : List Bool) (z : Fin (2^(c.n-p.k))) (j : Fin 2)
    (σ : Cycle.SignPattern 4) (w : Cycle.Walk hs.seedParameters.N 4) (i : Fin (p.J-1+1)) :
    |(Builder.columnData c hs bits z).E j σ w i| ≤ scoreRange c p := by
  refine (column_digit_abs_le c hs bits z j σ w i).trans ?_
  have hn : 8*Builder.occurrences c j*(c.n+1) ≤ scoreRange c p := by
    unfold scoreRange
    apply Nat.mul_le_mul
    · exact Nat.mul_le_mul_left 8 (occurrences_le_total c j)
    · omega
  exact_mod_cast hn

/-- `eq:testPhi`, paper/paper.tex: the combined unconditional
range retains the entire final error, including every arbitrary child. -/
theorem phi_le_scoreRange (bits : List Bool) (z : Fin (2^(c.n-p.k))) (j : Fin 2)
    (σ : Cycle.SignPattern 4) (w : Cycle.Walk hs.seedParameters.N 4) :
    |(Builder.columnData c hs bits z).phi (by norm_num) j σ w| ≤ scoreRange c p := by
  refine (column_phi_abs_le c hs bits z j σ w).trans ?_
  have hn : 8*Builder.occurrences c j*(p.M1+p.A) ≤ scoreRange c p := by
    unfold scoreRange
    apply Nat.mul_le_mul
    · exact Nat.mul_le_mul_left 8 (occurrences_le_total c j)
    · omega
  exact_mod_cast hn

/-- `eq:testE`–`eq:testPhi`, paper/paper.tex: the actual
pre-certification walk moments have a finite, explicit integer range. -/
theorem actual_walk_moment_abs_le (bits : List Bool) (z : Fin (2^(c.n-p.k)))
    (value : Walks.StructuralWalk (m := 4) (N := hs.seedParameters.N) (by norm_num)
      (Builder.columnData c hs bits z).structural → ℤ)
    (hv : ∀ w, |value w| ≤ scoreRange c p) :
    |Walks.maskedMoment (4*p.k)
      (fun w : Walks.StructuralWalk (m := 4) (N := hs.seedParameters.N) (by norm_num)
        (Builder.columnData c hs bits z).structural =>
        Walks.walkMaskPoly (by norm_num) (Builder.columnData c hs bits z).structural
          p.tau p.Xmax (Builder.columnData c hs bits z).X w.val) value| ≤
      ((p.N^8*maskRange p.Xmax (Builder.occurrences c 0+Builder.occurrences c 1)^8*
        scoreRange c p^(8*p.k) : ℕ) : ℤ) := by
  let D := Builder.columnData c hs bits z
  have hm (w : Walks.StructuralWalk (m := 4) (N := hs.seedParameters.N) (by norm_num) D.structural) :
      |Walks.walkMaskPoly (by norm_num) D.structural p.tau p.Xmax D.X w.val| ≤
        (maskRange p.Xmax (Builder.occurrences c 0+Builder.occurrences c 1)^8 : ℕ) := by
    have h := walkMaskPoly_abs_le D.structural p.tau p.Xmax
      (Builder.occurrences c 0+Builder.occurrences c 1) D.X (column_X_le c hs bits z) w.val
    simpa only [maskRange,Nat.cast_pow,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] using h
  have hc : Fintype.card (Walks.StructuralWalk (m := 4) (N := hs.seedParameters.N) (by norm_num) D.structural) ≤ p.N^8 := by
    calc
      _ ≤ Fintype.card (Cycle.Walk hs.seedParameters.N 4) := Fintype.card_subtype_le _
      _ = hs.seedParameters.N^8 := by simp [Cycle.Walk]
      _ = p.N^8 := by rw [Cells.ParameterRules.seed_N hs]
  have h := maskedMoment_abs_le (4*p.k)
    (maskRange p.Xmax (Builder.occurrences c 0+Builder.occurrences c 1)^8)
    (scoreRange c p) _ value hm hv
  refine h.trans ?_
  rw [show 2*(4*p.k)=8*p.k by omega]
  simp only [Nat.cast_mul,Nat.cast_pow]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact_mod_cast hc

/-- `prop:time`, paper/paper.tex: the actual arbitrary
witness walk moments fit the selected polynomial bit-height envelope. -/
theorem actual_walk_moment_selected_bound (B1 : ℕ)
    (hb : 1 ≤ c.radius*(c.n:ℚ)^B1) (bits : List Bool) (z : Fin (2^(c.n-p.k)))
    (value : Walks.StructuralWalk (m := 4) (N := hs.seedParameters.N) (by norm_num)
      (Builder.columnData c hs bits z).structural → ℤ)
    (hv : ∀ w, |value w| ≤ scoreRange c p) :
    |Walks.maskedMoment (4*p.k)
      (fun w : Walks.StructuralWalk (m := 4) (N := hs.seedParameters.N) (by norm_num)
        (Builder.columnData c hs bits z).structural =>
        Walks.walkMaskPoly (by norm_num) (Builder.columnData c hs bits z).structural
          p.tau p.Xmax (Builder.columnData c hs bits z).X w.val) value| ≤
      (2:ℤ)^(Cells.ParameterArithmetic.certificateBitEnvelope
        (Cells.ParameterArithmetic.preparationEnvelope B1 c.n)) := by
  refine (actual_walk_moment_abs_le c hs bits z value hv).trans ?_
  have h := Cells.ParameterRules.selected_walk_moment_power_bound hs B1 hb c.n le_rfl
  change p.N^8*maskRange p.Xmax (Builder.occurrences c 0+Builder.occurrences c 1)^8*
    scoreRange c p^(8*p.k) ≤ _ at h
  exact_mod_cast h

end NearQuarticWires.StageCert
