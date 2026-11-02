import Proof.Quartic.StageMain.SampleRecipe
import Proof.Quartic.StageGamma.BinaryPower

/-!
# Preparing the seed coefficients by binary operations

`imp:seed`, paper/paper.tex: a seed of eight field words
is decomposed by successive division by the physically computed radix
`2^ell`. The main pass, retains those coefficients for
all sample labels. This program changes only its named arithmetic state.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.SampleCells

open NearCubicGates.Close.Cells

theorem digitState_same (xs : List (Fin VV)) (a : DS VV MM) : Same a (digitState xs a) := by
  induction xs generalizing a with
  | nil => exact Same.set _ _ _
  | cons x xs ih =>
    exact ((Same.set _ _ _).trans ((Same.set _ _ _).trans (Same.set _ _ _))).trans
      (ih (digitStep x a))

def digitScratch : List (Fin VV) := vJ :: seed :: quotient :: coefficientRegisters

theorem splitSeed_frame (a : DS VV MM) : Fr a (digitState coefficientRegisters a) digitScratch := by
  intro y hy
  simp only [digitScratch, List.mem_cons, not_or] at hy
  exact digitState_env coefficientRegisters a y hy.2.2.2 hy.2.1 hy.2.2.1 hy.1

theorem splitSeed_constants (a : DS VV MM) (hc : Cst a) :
    Cst (digitState coefficientRegisters a) :=
  Cst.of_fr hc (splitSeed_frame a) (by decide)

theorem splitSeed_stored (r : SampleRequest) (a : DS VV MM)
    (hs : a.env seed = r.seed) (he : a.env ell = r.ell)
    (hm : a.env modulus = r.modulus) (hl : a.env label = r.label)
    (hb : a.env radix = 2 ^ r.ell) :
    SampleStored r (digitState coefficientRegisters a) := by
  have hf := splitSeed_frame a
  exact ⟨(hf ell (by decide)).trans he, (hf modulus (by decide)).trans hm,
    (hf label (by decide)).trans hl, splitSeed_sampler a r.ell r.seed hb hs⟩

def powerIndex : Fin VV := 94

def samplePrepare : St VV MM :=
  .seq (StageGamma.binaryPower powerIndex ell radix) (digitProgram coefficientRegisters)

def preparationScratch : List (Fin VV) := [powerIndex, radix] ++ digitScratch

theorem samplePrepare_run (r : SampleRequest) (C : Ctx) (a : DS VV MM)
    (hc : Cst a) (hs : a.env seed = r.seed) (he : a.env ell = r.ell)
    (hm : a.env modulus = r.modulus) (hl : a.env label = r.label)
    (hW : r.ell + 2 ≤ C.Wd) :
    Hs C samplePrepare a (5 * r.ell + 40) (fun b =>
      SampleStored r b ∧ Same a b ∧ Cst b ∧ Fr a b preparationScratch) := by
  have h1 := StageGamma.binaryPower_run C powerIndex ell radix (by decide) (by decide)
    (by decide) (by decide) a hc r.ell he (by omega)
  refine Hs.mono (Hs.seq (t1 := 5 * r.ell + 6) (t2 := 33) h1 ?_) (by omega) (fun _ h => h)
  intro b ⟨hb, hsame, hbc, hfr⟩
  refine (splitSeed_run C b (by rw [hb]; positivity) ?_).mono le_rfl ?_
  · rw [hb, Nat.mul_comm 2, ← pow_succ]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  · rintro d rfl
    refine ⟨splitSeed_stored r b ((hfr seed (by decide)).trans hs)
      ((hfr ell (by decide)).trans he) ((hfr modulus (by decide)).trans hm)
      ((hfr label (by decide)).trans hl) hb,
      hsame.trans (digitState_same coefficientRegisters b), splitSeed_constants b hbc, ?_⟩
    exact (hfr.weaken (fun x hx => List.mem_append_left _ hx)).trans
      ((splitSeed_frame b).weaken (fun x hx => List.mem_append_right _ hx))

end NearQuarticWires.StageMain.SampleCells
