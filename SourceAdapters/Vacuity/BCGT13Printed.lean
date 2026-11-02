import SourceAdapters.ShortPCP.TimeVerifiers
import SourceAdapters.Amplification.EncField
import Mathlib.Algebra.Field.ZMod

/-!
# Printed-text corrections in the BCGT13 transcription, with checked witnesses

`Statement.lean` (section 10) transcribes three passages of BCGT13 in a corrected form. The witnesses here are over
the field `F₈ = F₂[x]/(x³ + x + 1)` with the subspace basis `1, 2, 4`:

* Algorithm 21 (FindSubspPoly, p.126): the printed recurrence `Z(x²) + Z(a)·Z(x)` is not the vanishing polynomial
  over an extension field (`printed_recurrence_witness`: value `3`; `corrected_recurrence_witness`: value `0`);
  the transcription uses `Z_S(x) = ∏_{s ∈ S} (x − s)`.
* Algorithm 23 (SubspaceInterp, p.128): the printed base case `(x − α_{j2^κ})(x − α_{j2^κ+1})` is not an
  interpolation: over `ZMod 2` with the basis `[1]` and the values `0, 0` it takes the value `1` at the node `1`
  (`printed_base_not_interpolation`), while the zero polynomial interpolates (`intended_zero_interpolates`); the
  transcription uses the existential degree test (`Statement.lean`, section 10, item 5).
* §12.3.5 (`V_VRS`): with the equality in its printed orientation an honest instance is accepted on `1` of `8`
  coin strings (`swapped_honest_count`); with the orientation of Algorithm 12 step 2(g), which the transcription
  follows, on all `8` (`actual_honest_count`).
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option warningAsError true
namespace NearCubicGates.Adapters.Vacuity.BCGT13Printed
open NearCubicGates.Published.BCGT13
open NearCubicGates.Adapters.ShortPCP.Time
open NearCubicGates.Adapters.Amplification.Enc

structure F8 where
  code : Fin 8
  deriving DecidableEq, Fintype, Repr

def f (n : Nat) : F8 := ⟨⟨n % 8, Nat.mod_lt _ (by decide)⟩⟩
def add8 (a b : F8) : F8 := f (a.code.val ^^^ b.code.val)
def mul8 (a b : F8) : F8 := f (fmul 11 3 a.code.val b.code.val)
def inv8 (a : F8) : F8 := f (finv 11 3 a.code.val)
instance : Zero F8 := ⟨f 0⟩
instance : One F8 := ⟨f 1⟩
instance : Add F8 := ⟨add8⟩
instance : Neg F8 := ⟨id⟩
instance : Field F8 where
  zero := f 0
  one := f 1
  add := add8
  neg := id
  sub := add8
  nsmul := nsmulRec
  zsmul := zsmulRec
  mul := mul8
  inv := inv8
  add_assoc := by decide
  zero_add := by decide
  add_zero := by decide
  add_comm := by decide
  neg_add_cancel := by decide
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  mul_comm := by decide
  left_distrib := by decide
  right_distrib := by decide
  zero_mul := by decide
  mul_zero := by decide
  mul_inv_cancel := by decide
  inv_zero := by decide
  exists_pair_ne := ⟨f 0, f 1, by decide⟩
  nnqsmul := _
  qsmul := _

instance : CharP F8 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr (by decide)

def basis : List F8 := [f 1, f 2, f 4]
theorem basis_indep : Indep basis := by
  have h : ∀ v : Fin 8, sel basis v.val = 0 → v.val = 0 := by decide
  intro v hv
  exact h ⟨v, hv⟩

theorem empty_indep : Indep ([] : List F8) := by
  intro v hv _
  simpa using hv

/-- The executable `V_RS` used in these checks is the transcribed one. -/
theorem tested_RS_is_actual (d : Nat) :
    vRS T0 basis (f 0) d = vRSF basis (f 0) d := vRS_eq basis_indep _ _

/-- The executable `V_VRS` used in these checks is the transcribed one. -/
theorem tested_VRS_is_actual (d : Nat) :
    vVRS T0 basis (f 0) [] (f 1) d = vVRSF basis (f 0) [] (f 1) d :=
  vVRS_eq basis_indep _ empty_indep _ _

def counts (V : FlatVerifier F8) (B : List F8) (O : F8) (p : F8 → F8) (pi : Nat → F8) : Nat × Nat :=
  ((List.range (2^V.rand)).countP fun r =>
     V.accepts B O p (fun i => pi i.val) (fun i => r.testBit i.val), 2^V.rand)

/-- Algorithm 21 (FindSubspPoly, p.126) as printed: `Z(x) ↦ Z(x²) + Z(a)·Z(x)`. -/
def printedZ (B : List F8) : F8 → F8 :=
  B.foldl (fun z a => fun x => z (x*x) + z a * z x) id
/-- The recurrence that computes the vanishing polynomial `Z_S(x) = ∏_{s ∈ S} (x − s)`:
`Z(x) ↦ Z(x)² + Z(a)·Z(x)`. -/
def squareZ (B : List F8) : F8 → F8 :=
  B.foldl (fun z a => fun x => z x * z x + z a * z x) id

/-- `V_VRS` with the equality of §12.3.5 (p.84) in its printed orientation, `p̃(α) = Z_H(α)·p(α)`, and the
query map of the transcribed verifier. -/
def swappedVRS : FlatVerifier F8 :=
  let V := vRSF basis (f 0) 0
  { vVRSF basis (f 0) [] (f 1) 1 with
    D := fun r ans => V.D r ans &&
      decide (ans (V.query+2) = zFast ([] : List F8) (getRandElt basis (f 0) (r.take 3) + 1) * ans (V.query+1)) }
/-- The transcribed vanishing polynomial vanishes at a point of the subspace (`F₈`, basis `1, 2, 4`). -/
theorem actual_product_witness : zEval basis (f 0) (f 2) = f 0 := by decide
/-- The printed recurrence of Algorithm 21 gives `3` at the same point, so it is not the vanishing polynomial. -/
theorem printed_recurrence_witness : printedZ basis (f 2) = f 3 := by decide
/-- The corrected recurrence gives `0` there. -/
theorem corrected_recurrence_witness : squareZ basis (f 2) = f 0 := by decide
/-- The two recurrences differ over `F₈`. -/
theorem printed_and_corrected_differ : printedZ basis (f 2) ≠ squareZ basis (f 2) := by decide
/-- With the printed orientation of §12.3.5, an honest instance is accepted on `1` of `8` coin strings. -/
theorem swapped_honest_count : counts swappedVRS basis (f 0) (fun x => x+1) (fun _ => 1) = (1,8) := by decide
/-- With the orientation of Algorithm 12 step 2(g) (the transcribed `V_VRS`), it is accepted on all `8`. -/
theorem actual_honest_count : counts (vVRSF basis (f 0) [] (f 1) 1) basis (f 0)
    (fun x => x+1) (fun _ => 1) = (8,8) := by decide

section Algorithm23

open Polynomial

/-- Algorithm 23 (SubspaceInterp, p.128) as printed, at `j = 0`, `κ = 1` and the values `α_0 = a0`, `α_1 = a1`:
`(x − a0)·(x − a1)`. -/
noncomputable def alg23PrintedBase (a0 a1 : ZMod 2) : Polynomial (ZMod 2) :=
  (X - C a0) * (X - C a1)

/-- `[1]` with offset `0` is a basis of `ZMod 2`. -/
theorem alg23_basis_valid : IsBasis ([1] : List (ZMod 2)) 0 := by
  unfold IsBasis; decide

/-- `1` is a node of the subspace spanned by `[1]`. -/
theorem alg23_one_is_node : (1 : ZMod 2) ∈ span ([1] : List (ZMod 2)) 0 := by decide

/-- The printed base case takes the value `1` at the node `1`. -/
theorem alg23_printed_base_wrong_value : (alg23PrintedBase 0 0).eval (1 : ZMod 2) = 1 := by
  simp [alg23PrintedBase]

/-- The printed base case does not interpolate the values `0, 0` on the subspace. -/
theorem printed_base_not_interpolation :
    ¬ ∀ x ∈ span ([1] : List (ZMod 2)) 0, (alg23PrintedBase 0 0).eval x = 0 := by
  intro h
  have hbad := h 1 alg23_one_is_node
  rw [alg23_printed_base_wrong_value] at hbad
  exact one_ne_zero hbad

/-- The zero polynomial, of degree below `2`, interpolates them. -/
theorem intended_zero_interpolates :
    (0 : Polynomial (ZMod 2)).natDegree < 2 ∧
    ∀ x ∈ span ([1] : List (ZMod 2)) 0, (0 : Polynomial (ZMod 2)).eval x = 0 := by
  simp

end Algorithm23

end NearCubicGates.Adapters.Vacuity.BCGT13Printed
