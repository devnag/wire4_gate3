import Proof.Quartic.StageRecovery.FamilyHeader
import Proof.Quartic.StageRecovery.FieldSequence
import Proof.Gates.Cells.Arith

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: a fixed literal
increment block has no input-dependent precomputed register value. -/
def incrementRegister (x : Fin VV) : ℕ → St VV MM
  | 0 => skipS
  | n + 1 => .seq (.op (.inc x)) (incrementRegister x n)

/-- `lem:print`, paper/paper.tex: each fixed setup
increment is an actual charged binary operation. -/
theorem incrementRegister_spec (C : Ctx) (x : Fin VV) (hx : x ≠ vJ) (n : ℕ) (a : DS VV MM)
    (hfit : a.env x + n < 2 ^ C.Wd) :
    Hs C (incrementRegister x n) a (2 * n + 1) (fun b =>
      b.env x = a.env x + n ∧ b.sh = a.sh ∧ Fr a b [x, vJ]) := by
  induction n generalizing a with
  | zero =>
      refine (skip_spec a).mono (by simp) ?_
      rintro b rfl
      exact ⟨by simp [DS.set_env_ne _ _ hx], rfl, Fr.set _ _ (by simp)⟩
  | succ n ih =>
      unfold incrementRegister
      refine (Hs.seq (t2 := 2 * n + 1) (hs_inc C x a (by omega)) fun b hb => ?_).mono
        (by omega) (fun _ h => h)
      subst b
      refine (ih _ (by simp; omega)).mono le_rfl ?_
      rintro b ⟨h1, h2, h3⟩
      exact ⟨by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h1,
        h2, Fr.trans (Fr.set _ _ (by simp)) h3⟩

/-- `lem:print`, paper/paper.tex: the family field
width is formed by actual addition of arity, degree and eight markers. -/
def familyWidthProgram : St VV MM :=
  .seq (.op (.copy FixedBits.width arityVar))
    (.seq (.op (.add FixedBits.width familyBoundVar)) (incrementRegister FixedBits.width 8))

/-- `lem:print`, paper/paper.tex: physical width
construction retains all original request values and input bytes. -/
theorem familyWidthProgram_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (V D : ℕ) (hV : a.env arityVar = V) (hD : a.env familyBoundVar = D)
    (hfit : V + D + 8 < 2 ^ C.Wd) :
    Hs C familyWidthProgram a 21 (fun b => b.env FixedBits.width = V + D + 8 ∧
      b.sh = a.sh ∧ Cst b ∧ Fr a b [FixedBits.width, vJ]) := by
  unfold familyWidthProgram
  refine Hs.seq (t2 := 19) (hs_copy C FixedBits.width arityVar a (by decide)) fun b hb => ?_
  subst b
  refine Hs.seq (t2 := 17) (hs_add C FixedBits.width familyBoundVar _ (by decide)
    (by simp (config := {decide := true}) [DS.set, hV, hD]; omega)) fun b hb => ?_
  subst b
  refine (incrementRegister_spec C FixedBits.width (by decide) 8 _
    (by simp (config := {decide := true}) [DS.set, hV, hD]; exact hfit)).mono (by norm_num) ?_
  rintro b ⟨h1, h2, h3⟩
  have hf : Fr a b [FixedBits.width, vJ] := Fr.trans (Fr.set _ _ (by simp))
    (Fr.trans (Fr.set _ _ (by simp)) h3)
  exact ⟨by simpa (config := {decide := true}) [DS.set, hV, hD] using h1,
    h2, Cst.of_fr hc hf (by decide), hf⟩

/-- `lem:print`, paper/paper.tex: the original support
radix is exponentiated by an actual finite binary program. -/
def familyRadixProgram : St VV MM := powP v2 arityVar coordinateBaseVar

/-- `lem:print`, paper/paper.tex: computing the support
radix charges every multiply-by-two step and retains all source metadata. -/
theorem familyRadixProgram_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (V : ℕ) (hV : a.env arityVar = V) (hW : V < C.Wd) :
    Hs C familyRadixProgram a (7 * V + 8) (fun b => b.env coordinateBaseVar = 2 ^ V ∧
      b.sh = a.sh ∧ Cst b ∧ Fr a b [coordinateBaseVar, a1, c4]) := by
  unfold familyRadixProgram
  refine (powP_spec v2 arityVar coordinateBaseVar (by decide) a
    (by intro k hk; rw [hc.two]; exact Nat.pow_lt_pow_right (by decide) (by rw [hV] at hk; omega))
    (by rw [hV]; exact (lt_of_lt_of_le hW (Nat.lt_two_pow_self.le)))
    (Nat.one_lt_two_pow (by omega))).mono (by rw [hV]; omega) ?_
  rintro b ⟨h1, h2, h3⟩
  exact ⟨by simpa only [hc.two, hV] using h1, h2, Cst.of_fr hc h3 (by decide), h3⟩

/-- `lem:print`, paper/paper.tex: the finite support
mask is formed by subtracting the initialized one from its actual radix. -/
def familyMaskProgram : St VV MM :=
  .seq (.op (.copy familyMaskVar coordinateBaseVar)) (.op (.sub familyMaskVar v1))

/-- `lem:print`, paper/paper.tex: mask initialization
uses literal binary copying and subtraction, preserving every other field. -/
theorem familyMaskProgram_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (V : ℕ) (hbase : a.env coordinateBaseVar = 2 ^ V) :
    Hs C familyMaskProgram a 3 (fun b => b.env familyMaskVar = 2 ^ V - 1 ∧
      b.sh = a.sh ∧ Cst b ∧ Fr a b [familyMaskVar]) := by
  unfold familyMaskProgram
  refine Hs.seq (t2 := 1) (hs_copy C familyMaskVar coordinateBaseVar a (by decide)) fun b hb => ?_
  subst b
  refine (hs_sub C familyMaskVar v1 _ (by decide)
    (by simp (config := {decide := true}) [DS.set, hc.one, hbase]; exact Nat.one_le_two_pow)).mono le_rfl ?_
  rintro b rfl
  have hf : Fr a ((a.set familyMaskVar (a.env coordinateBaseVar)).set familyMaskVar
      ((a.set familyMaskVar (a.env coordinateBaseVar)).env familyMaskVar -
        (a.set familyMaskVar (a.env coordinateBaseVar)).env v1)) [familyMaskVar] :=
    Fr.trans (Fr.set _ _ (by simp)) (Fr.set _ _ (by simp))
  exact ⟨by simp (config := {decide := true}) [DS.set, hbase, hc.one], rfl,
    Cst.of_fr hc hf (by decide), hf⟩

end NearQuarticWires.StageRecovery
