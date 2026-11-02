import Proof.Quartic.StagePullback.SignedTarget

set_option autoImplicit false

namespace NearQuarticWires.StagePullback.SignedCoefficients

open NearCubicGates.Close.Cells
open NearCubicGates.Close.WordPrograms

def scratch : List (Fin VV) := [value, magnitude, sign, positive, negative, vJ]

/-- `imp:pullback`, paper/paper.tex: the actual
canonical flip bit controls both signed weight negation and its exact
affine target correction. -/
def program : St VV MM :=
  .seq splitProgram (.ite (.eq Flips.accumulator v1)
    (.seq shiftProgram negateProgram) skipS)

/-- `imp:pullback` and `prop:time`, paper/paper.tex: one original signed coefficient is physically transformed
to its exact affine row coefficient while subtracting precisely its
flipped contribution from the target accumulator. -/
theorem program_run_mass (C : Ctx) (a : DS VV MM) (hc : Cst a) (z : ℤ) (f : Bool)
    (hv : a.env value = SInt.encS z) (hf : a.env Flips.accumulator = f.toNat)
    (hwidth : 2 ≤ C.Wd) (hfit : SInt.encS z + 1 < 2 ^ C.Wd)
    (hpfit : a.env positive + z.natAbs < 2 ^ C.Wd)
    (hnfit : a.env negative + z.natAbs < 2 ^ C.Wd) :
    Hs C program a 10 (fun b =>
      b.env value = SInt.encS (if f then -z else z) ∧
      (b.env positive : ℤ) - b.env negative =
        (a.env positive : ℤ) - a.env negative - (if f then z else 0) ∧
      b.env positive + b.env negative =
        a.env positive + a.env negative + (if f then z.natAbs else 0) ∧
      b.sh = a.sh ∧ Fr a b scratch) := by
  unfold program
  refine Hs.mono (Hs.seq (t1 := 1) (t2 := 7)
    (splitProgram_run C a hc z hv hwidth)
    (fun b ⟨hm, hs, hbsh, hbfr⟩ => ?_)) (by omega) (fun _ h => h)
  have hbc : Cst b := hc.of_fr hbfr (by decide)
  have hbv : b.env value = SInt.encS z := (hbfr _ (by decide)).trans hv
  have hbf : b.env Flips.accumulator = f.toNat := (hbfr _ (by decide)).trans hf
  have hbp : b.env positive = a.env positive := hbfr _ (by decide)
  have hbn : b.env negative = a.env negative := hbfr _ (by decide)
  have hba : Fr a b scratch := hbfr.weaken (by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl <;> decide)
  cases f with
  | false =>
    refine Hs.mono (Hs.iteF (show Flips.accumulator ≠ v1 by decide)
      (by simp [Cnd.eval, hbf, hbc.one]) (skip_spec b)) (by omega) ?_
    rintro d rfl
    refine ⟨?_, ?_, ?_, hbsh, hba.trans (Fr.set b _ (by decide))⟩
    · simpa only [Bool.false_eq_true, if_false,
        DS.set_env_ne _ _ (by decide : value ≠ vJ)] using hbv
    · rw [DS.set_env_ne _ _ (by decide : positive ≠ vJ),
        DS.set_env_ne _ _ (by decide : negative ≠ vJ), hbp, hbn]
      simp
    · rw [DS.set_env_ne _ _ (by decide : positive ≠ vJ),
        DS.set_env_ne _ _ (by decide : negative ≠ vJ), hbp, hbn]
      simp
  | true =>
    refine Hs.iteT (show Flips.accumulator ≠ v1 by decide)
      (by simp [Cnd.eval, hbf, hbc.one]) ?_
    refine Hs.seq (t1 := 2) (t2 := 3)
      (shiftProgram_run C b hbc z hm hs
        (by rw [hbp]; exact hpfit) (by rw [hbn]; exact hnfit)) ?_
    rintro c ⟨hpos, hneg, hdiff, hcsh, hcfr⟩
    have hcc : Cst c := hbc.of_fr hcfr (by decide)
    have hcv : c.env value = SInt.encS z := (hcfr _ (by decide)).trans hbv
    have hcs : c.env sign = if z < 0 then 1 else 0 := (hcfr _ (by decide)).trans hs
    have hcb : Fr b c scratch := hcfr.weaken (by
      intro y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl <;> decide)
    have hmass : c.env positive + c.env negative = a.env positive + a.env negative + z.natAbs := by
      rw [hpos, hneg, hbp, hbn]
      split_ifs <;> omega
    refine Hs.mono (negateProgram_run C c hcc z hcv hcs hfit) le_rfl ?_
    rintro d ⟨hdv, hdsh, hdfr⟩
    refine ⟨by simpa using hdv, ?_, ?_, hdsh.trans (hcsh.trans hbsh),
      hba.trans (hcb.trans (hdfr.weaken (by
        intro y hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl <;> decide)))⟩
    rw [hdfr _ (by decide : positive ∉ [value, vJ]),
      hdfr _ (by decide : negative ∉ [value, vJ]), hdiff, hbp, hbn]
    rfl
    · rw [hdfr _ (by decide : positive ∉ [value, vJ]),
        hdfr _ (by decide : negative ∉ [value, vJ]), hmass]
      rfl

/-- `imp:pullback`, paper/paper.tex: the physical
signed coefficient update returns its exact affine weight and target. -/
theorem program_run (C : Ctx) (a : DS VV MM) (hc : Cst a) (z : ℤ) (f : Bool)
    (hv : a.env value = SInt.encS z) (hf : a.env Flips.accumulator = f.toNat)
    (hwidth : 2 ≤ C.Wd) (hfit : SInt.encS z + 1 < 2 ^ C.Wd)
    (hpfit : a.env positive + z.natAbs < 2 ^ C.Wd)
    (hnfit : a.env negative + z.natAbs < 2 ^ C.Wd) :
    Hs C program a 10 (fun b =>
      b.env value = SInt.encS (if f then -z else z) ∧
      (b.env positive : ℤ) - b.env negative =
        (a.env positive : ℤ) - a.env negative - (if f then z else 0) ∧
      b.sh = a.sh ∧ Fr a b scratch) :=
  Hs.mono (program_run_mass C a hc z f hv hf hwidth hfit hpfit hnfit) le_rfl
    (fun _ ⟨hv, hd, _, hs, hf⟩ => ⟨hv, hd, hs, hf⟩)

end NearQuarticWires.StagePullback.SignedCoefficients
