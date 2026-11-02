import Proof.Quartic.Walks.MaskCertificate
import Proof.Gates.ScoreBox
import Mathlib.Data.Int.Interval

set_option autoImplicit false

namespace NearQuarticWires.Walks

open scoped BigOperators

/-- Paper `sec:walks`/`eq:testX`--`eq:testPhi`, paper/paper.tex:
all data of ONE column, with actual signed cycle sums and arbitrary proposed
integer chains. `J` is the zero-based last stage (the paper has `J+1` stages). -/
structure WalkData (N m J : ℕ) where
  structural : Sampler.Cell N → Bool
  tau : ℕ
  Xmax : ℕ
  X : Sampler.Cell N → ℕ
  circuits : Finset (Fin 2)
  residual : Fin 2 → Sampler.Cell N → ℤ
  values : Fin 2 → Cycle.SignPattern m → Cycle.Walk N m → ℕ → ℤ
  rate : ℕ → ℤ
  M : ℤ
  A : ℤ
  hE : ℕ
  Lambda : ℕ

/-- Paper `sec:walks`, paper/paper.tex: the actual `Y_{j,sigma}(z,w)`. -/
def WalkData.Y {N m J : ℕ} (D : WalkData N m J) (hm : 0 < m)
    (j : Fin 2) (sigma : Cycle.SignPattern m) (w : Cycle.Walk N m) : ℤ :=
  Cycle.walkSum hm (D.residual j) sigma w

/-- Paper `sec:walks`, paper/paper.tex: the proposed nested-chain digits,
without a sampling-honesty assumption. -/
def WalkData.E {N m J : ℕ} (D : WalkData N m J)
    (j : Fin 2) (sigma : Cycle.SignPattern m) (w : Cycle.Walk N m) (r : Fin (J + 1)) : ℤ :=
  NearCubicGates.CountingCore.proposedDigit D.rate (D.values j sigma w) r.val

/-- Paper `sec:walks`, paper/paper.tex: the actual final walk-sum error. -/
def WalkData.phi {N m J : ℕ} (D : WalkData N m J) (hm : 0 < m)
    (j : Fin 2) (sigma : Cycle.SignPattern m) (w : Cycle.Walk N m) : ℤ :=
  D.M * D.values j sigma w J - D.A * D.Y hm j sigma w

/-- Paper `eq:testX`--`eq:testPhi`, paper/paper.tex: the LITERAL certification
tests, only for the concrete sign patterns with `kappa sigma != 0`. The
population test is retained separately and used before the other tests. -/
structure ColumnCertificate {N m J : ℕ} (hm : 0 < m) (k : ℕ)
    (D : WalkData N m J) : Prop where
  population : momentSum k (fun x : StructuralPoint D.structural => (D.X x.val : ℤ)) <
    ((D.Xmax + 1 : ℕ) : ℤ) ^ (2 * k)
  digits : ∀ j ∈ D.circuits, ∀ sigma : Cycle.SignPattern m,
    Cycle.kappa m sigma ≠ 0 → ∀ r : Fin (J + 1),
      maskedMoment (m * k)
        (fun w : StructuralWalk hm D.structural =>
          walkMaskPoly hm D.structural D.tau D.Xmax D.X w.val)
        (fun w => D.E j sigma w.val r) < (D.hE : ℤ) ^ (2 * (m * k))
  finalError : ∀ j ∈ D.circuits, ∀ sigma : Cycle.SignPattern m,
    Cycle.kappa m sigma ≠ 0 →
      maskedMoment (m * k)
        (fun w : StructuralWalk hm D.structural =>
          walkMaskPoly hm D.structural D.tau D.Xmax D.X w.val)
        (fun w => D.phi hm j sigma w.val) < (D.Lambda : ℤ) ^ (2 * (m * k))

/-- Paper `lem:certify`(a), paper/paper.tex: the first test makes the exact
walk-polynomial mask agree with the literal integer mask on EVERY walk. -/
theorem certified_walk_mask_exact {N m J : ℕ} (hm : 0 < m) (k : ℕ)
    (D : WalkData N m J) (cert : ColumnCertificate hm k D) (w : Cycle.Walk N m) :
    walkMaskPoly hm D.structural D.tau D.Xmax D.X w =
      walkMaskInt hm D.structural D.tau D.X w :=
  testX_walkMaskPoly_exact hm D.structural k D.tau D.Xmax D.X cert.population w

/-- Paper `lem:certify`(b), paper/paper.tex: every retained walk has ALL
digits in the strict window, only for patterns actually tested (`kappa != 0`). -/
theorem certified_digit_bound {N m J : ℕ} (hm : 0 < m) (k : ℕ)
    (D : WalkData N m J) (cert : ColumnCertificate hm k D)
    (j : Fin 2) (hj : j ∈ D.circuits) (sigma : Cycle.SignPattern m)
    (hsigma : Cycle.kappa m sigma ≠ 0) (r : Fin (J + 1))
    (w : Cycle.Walk N m) (hw : walkMaskInt hm D.structural D.tau D.X w = 1) :
    (D.E j sigma w r).natAbs < D.hE := by
  let ws : StructuralWalk hm D.structural :=
    ⟨w, retained_walk_structural hm D.structural D.tau D.X w hw⟩
  have hbool : ∀ v : StructuralWalk hm D.structural,
      walkMaskPoly hm D.structural D.tau D.Xmax D.X v.val = 0 ∨
        walkMaskPoly hm D.structural D.tau D.Xmax D.X v.val = 1 := by
    intro v
    rw [certified_walk_mask_exact hm k D cert]
    exact walkMaskInt_zero_or_one hm D.structural D.tau D.X v.val
  have hkeep : walkMaskPoly hm D.structural D.tau D.Xmax D.X ws.val = 1 := by
    change walkMaskPoly hm D.structural D.tau D.Xmax D.X w = 1
    rw [certified_walk_mask_exact hm k D cert, hw]
  exact masked_moment_sound (m * k) D.hE _ _ hbool
    (cert.digits j hj sigma hsigma r) ws hkeep

/-- Paper `lem:certify`(b), paper/paper.tex: the final error is certified
on every retained walk, without assuming the proposed chain was sampled. -/
theorem certified_final_error_bound {N m J : ℕ} (hm : 0 < m) (k : ℕ)
    (D : WalkData N m J) (cert : ColumnCertificate hm k D)
    (j : Fin 2) (hj : j ∈ D.circuits) (sigma : Cycle.SignPattern m)
    (hsigma : Cycle.kappa m sigma ≠ 0)
    (w : Cycle.Walk N m) (hw : walkMaskInt hm D.structural D.tau D.X w = 1) :
    (D.phi hm j sigma w).natAbs < D.Lambda := by
  let ws : StructuralWalk hm D.structural :=
    ⟨w, retained_walk_structural hm D.structural D.tau D.X w hw⟩
  have hbool : ∀ v : StructuralWalk hm D.structural,
      walkMaskPoly hm D.structural D.tau D.Xmax D.X v.val = 0 ∨
        walkMaskPoly hm D.structural D.tau D.Xmax D.X v.val = 1 := by
    intro v
    rw [certified_walk_mask_exact hm k D cert]
    exact walkMaskInt_zero_or_one hm D.structural D.tau D.X v.val
  have hkeep : walkMaskPoly hm D.structural D.tau D.Xmax D.X ws.val = 1 := by
    change walkMaskPoly hm D.structural D.tau D.Xmax D.X w = 1
    rw [certified_walk_mask_exact hm k D cert, hw]
  exact masked_moment_sound (m * k) D.Lambda _ _ hbool
    (cert.finalError j hj sigma hsigma) ws hkeep

/-- Paper `lem:certify`(c), paper/paper.tex: a full digit vector in the
certified strict range is determined by its residues for each admitted prime. -/
theorem certified_digits_mod_iff {N m J : ℕ} (hm : 0 < m) (k : ℕ)
    (D : WalkData N m J) (cert : ColumnCertificate hm k D)
    (j : Fin 2) (hj : j ∈ D.circuits) (sigma : Cycle.SignPattern m)
    (hsigma : Cycle.kappa m sigma ≠ 0)
    (w : Cycle.Walk N m) (hw : walkMaskInt hm D.structural D.tau D.X w = 1)
    (delta : Fin (J + 1) → ℤ) (hdelta : ∀ r, (delta r).natAbs < D.hE)
    (p : ℤ) (hwidth : 2 * (D.hE : ℤ) - 1 ≤ p) :
    (∀ r, D.E j sigma w r ≡ delta r [ZMOD p]) ↔ ∀ r, D.E j sigma w r = delta r := by
  constructor
  · intro hmod r
    have hd := certified_digit_bound hm k D cert j hj sigma hsigma r w hw
    have he : |D.E j sigma w r| < (D.hE : ℤ) := by
      simpa only [Int.natCast_natAbs] using
        (show ((D.E j sigma w r).natAbs : ℤ) < D.hE from by exact_mod_cast hd)
    have hf : |delta r| < (D.hE : ℤ) := by
      simpa only [Int.natCast_natAbs] using
        (show ((delta r).natAbs : ℤ) < D.hE from by exact_mod_cast hdelta r)
    have he' := abs_lt.mp he
    have hf' := abs_lt.mp hf
    apply NearCubicGates.CountingCore.centered_digit_residue_unique
      (D.E j sigma w r) (delta r) 0 D.hE p
    · simpa using he'.1
    · simpa using he'.2
    · simpa using hf'.1
    · simpa using hf'.2
    · exact hwidth
    · exact (hmod r).eq
  · intro he r
    rw [he r]

/-- Paper `lem:certify`(d), paper/paper.tex: the literal integer
`K(delta)=sum A_r delta_r`, evaluated by the already proved telescoping recursion. -/
def digitValue {J : ℕ} (rate : ℕ → ℤ) (delta : Fin (J + 1) → ℤ) : ℤ :=
  NearCubicGates.CountingCore.reconstruct rate
    (NearCubicGates.CertifiedScoreSupport.extendDigits delta) J

/-- Paper `imp:chain`/`lem:certify`(d), paper/paper.tex: arbitrary
proposed vectors telescope on a digit class; no nested-sampling assumption. -/
theorem last_value_on_digits {N m J : ℕ} (D : WalkData N m J)
    (j : Fin 2) (sigma : Cycle.SignPattern m) (w : Cycle.Walk N m)
    (delta : Fin (J + 1) → ℤ) (hdigits : ∀ r, D.E j sigma w r = delta r) :
    D.values j sigma w J = digitValue D.rate delta := by
  rw [← NearCubicGates.CountingCore.reconstruct_proposedDigit D.rate (D.values j sigma w) J]
  apply NearCubicGates.CertifiedScoreSupport.reconstruct_ext_upto
  intro r hr
  have h := hdigits ⟨r, by omega⟩
  simpa only [WalkData.E, NearCubicGates.CertifiedScoreSupport.extendDigits,
    dif_pos (by omega : r < J + 1)] using h

/-- Paper `lem:certify`(d), paper/paper.tex: the FULL computed integer box,
including both strict-error endpoint corrections and clipping by the true range. -/
noncomputable def fullBox (center A Lambda bound : ℤ) : Finset ℤ :=
  Finset.Icc
    (max (NearCubicGates.ScoreBox.lower center A 0 Lambda) (-bound))
    (min (NearCubicGates.ScoreBox.upper center A 0 Lambda) bound)

/-- Paper `lem:certify`(d), paper/paper.tex: every retained walk in a fixed
digit class lies in the FULL clipped box, for each active sign pattern. -/
theorem certified_walk_sum_in_box {N m J : ℕ} (hm : 0 < m) (k : ℕ)
    (D : WalkData N m J) (cert : ColumnCertificate hm k D) (hA : 0 < D.A)
    (j : Fin 2) (hj : j ∈ D.circuits) (sigma : Cycle.SignPattern m)
    (hsigma : Cycle.kappa m sigma ≠ 0) (G : ℕ)
    (hR : ∀ x, |D.residual j x| ≤ G)
    (w : Cycle.Walk N m) (hw : walkMaskInt hm D.structural D.tau D.X w = 1)
    (delta : Fin (J + 1) → ℤ) (hdigits : ∀ r, D.E j sigma w r = delta r) :
    D.Y hm j sigma w ∈ fullBox (D.M * digitValue D.rate delta) D.A D.Lambda
      ((2 * m : ℕ) * (G : ℤ)) := by
  have hp := certified_final_error_bound hm k D cert j hj sigma hsigma w hw
  have hid : D.phi hm j sigma w =
      D.M * digitValue D.rate delta - D.A * D.Y hm j sigma w := by
    rw [WalkData.phi, last_value_on_digits D j sigma w delta hdigits]
  rw [hid] at hp
  have hmag : (((D.M * digitValue D.rate delta - D.A *
      (D.Y hm j sigma w - 0)).natAbs : ℕ) : ℤ) < D.Lambda := by
    simpa only [sub_zero] using (show
      (((D.M * digitValue D.rate delta - D.A * D.Y hm j sigma w).natAbs : ℕ) : ℤ) <
        (D.Lambda : ℤ) from by exact_mod_cast hp)
  have hb := NearCubicGates.ScoreBox.score_in_box _ _ 0 _ _ hA hmag
  have hr := abs_le.mp (Cycle.abs_walkSum_le hm (D.residual j) G hR sigma w)
  apply Finset.mem_Icc.mpr
  exact ⟨max_le hb.1 hr.1, le_min hb.2 hr.2⟩

/-- Paper `lem:certify`(d), paper/paper.tex: clipping never enlarges the
computed box, whose full integer cardinality is at most the public window. -/
theorem fullBox_card_le (center A Lambda bound : ℤ) (L : ℕ)
    (hA : 0 < A) (hwidth : 2 * Lambda - 2 ≤ ((L : ℤ) - 1) * A) :
    (fullBox center A Lambda bound).card ≤ L := by
  have hsub : fullBox center A Lambda bound ⊆
      Finset.Icc (NearCubicGates.ScoreBox.lower center A 0 Lambda)
        (NearCubicGates.ScoreBox.upper center A 0 Lambda) := by
    intro y hy
    have h := Finset.mem_Icc.mp hy
    exact Finset.mem_Icc.mpr ⟨(le_max_left _ _).trans h.1, h.2.trans (min_le_left _ _)⟩
  have hb := NearCubicGates.ScoreBox.boxCount_le center A 0 Lambda L hA (by omega) hwidth
  apply (Finset.card_le_card hsub).trans
  simpa only [Int.card_Icc, NearCubicGates.ScoreBox.boxCount, Int.toNat_natCast,
    sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hb

end NearQuarticWires.Walks
