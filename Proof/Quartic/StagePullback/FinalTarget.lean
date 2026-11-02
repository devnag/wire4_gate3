import Proof.Quartic.StagePullback.TargetAccumulation
import Proof.Quartic.StagePullback.RowCoordinate

set_option autoImplicit false

namespace NearQuarticWires.StagePullback.SignedCoefficients

open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicGates.Close.Cells
open NearCubicGates.Close.WordPrograms

def targetScratch : List (Fin VV) := [value, magnitude, sign, positive, negative]

/-- `imp:pullback`, paper/paper.tex: decode the
original target, insert it into the affine accumulators, then physically
cancel and canonically encode their exact signed difference. -/
def finalizeTargetProgram : St VV MM :=
  .seq splitProgram (.seq insertTargetProgram targetProgram)

/-- `imp:pullback` and `prop:time`, paper/paper.tex: exact original-target insertion and final cancellation
are performed by literal binary operations with a constant source clock. -/
theorem finalizeTargetProgram_run (C : Ctx) (a : DS VV MM) (hc : Cst a) (t : ℤ)
    (hv : a.env value = SInt.encS t) (hwidth : 2 ≤ C.Wd)
    (hfit : 2 * (a.env positive + a.env negative + t.natAbs) + 1 < 2 ^ C.Wd) :
    Hs C finalizeTargetProgram a 16 (fun b =>
      b.env value = SInt.encS ((a.env positive : ℤ) - a.env negative + t) ∧
      b.env positive + b.env negative = a.env positive + a.env negative + t.natAbs ∧
      b.sh = a.sh ∧ Cst b ∧ Fr a b targetScratch) := by
  unfold finalizeTargetProgram
  refine Hs.mono (Hs.seq (t1 := 1) (t2 := 11) (splitProgram_run C a hc t hv hwidth)
    (fun b ⟨hm, hs, hbsh, hbfr⟩ => ?_)) (by omega) (fun _ h => h)
  have hbc : Cst b := hc.of_fr hbfr (by decide)
  have hbp : b.env positive = a.env positive := hbfr _ (by decide)
  have hbn : b.env negative = a.env negative := hbfr _ (by decide)
  have hba : Fr a b targetScratch := hbfr.weaken (by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl <;> decide)
  refine Hs.seq (t1 := 2) (t2 := 8) (insertTargetProgram_run C b hbc t hm hs
    (by rw [hbp]; omega) (by rw [hbn]; omega)) ?_
  rintro c ⟨hcdiff, hcmass, hcsh, hcfr⟩
  have hcc : Cst c := hbc.of_fr hcfr (by decide)
  have hcb : Fr b c targetScratch := hcfr.weaken (by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl <;> decide)
  refine Hs.mono (targetProgram_run C c (by rw [hcmass, hbp, hbn]; exact hfit)) le_rfl ?_
  rintro d ⟨hdv, hdsh, hdfr⟩
  have hdc : Cst d := hcc.of_fr hdfr (by decide)
  refine ⟨?_, ?_, hdsh.trans (hcsh.trans hbsh), hdc,
    hba.trans (hcb.trans (hdfr.weaken (by
      intro y hy
      simp only [List.mem_singleton] at hy
      subst hy
      decide)))⟩
  · rw [hdv, hcdiff, hbp, hbn]
  · rw [hdfr _ (by decide : positive ∉ [value]), hdfr _ (by decide : negative ∉ [value]),
      hcmass, hbp, hbn]

/-- `imp:pullback`, paper/paper.tex: the final source
field is read from the original child row before exact target assembly. -/
def originalTargetProgram : St VV MM :=
  .seq (StageGamma.fixedRead NativeRows.fieldWidth value) finalizeTargetProgram

/-- `imp:pullback` and `prop:time`, paper/paper.tex: the original fixed signed target, including its original
threshold convention, physically becomes the exact adjusted signed target
while all native coefficient records are preserved. -/
theorem originalTargetProgram_run_frame (C : Ctx) (a : DS VV MM) (hc : Cst a) (t : ℤ)
    (Lin : ℕ) (rest : List Bool) (hwidth : 2 ≤ C.Wd)
    (hfield : a.env NativeRows.fieldWidth = Lin) (hfieldWidth : Lin + 1 ≤ C.Wd)
    (ht : SInt.encS t < 2 ^ Lin)
    (hin : C.inp.drop a.ip = binary Lin (SInt.encS t) ++ rest)
    (hfit : 2 * (a.env positive + a.env negative + t.natAbs) + 1 < 2 ^ C.Wd) :
    Hs C originalTargetProgram a (10 * Lin + 40) (fun b =>
      b.env value = SInt.encS ((a.env positive : ℤ) - a.env negative + t) ∧
      b.env positive + b.env negative = a.env positive + a.env negative + t.natAbs ∧
      b.ip = a.ip + Lin ∧ b.out = a.out ∧ b.ram = a.ram ∧ b.rc = a.rc ∧ Cst b ∧
      Fr a b (StageGamma.fixedReadScratch value ++ targetScratch)) := by
  unfold originalTargetProgram
  refine Hs.mono (Hs.seq (t1 := 10 * Lin + 18) (t2 := 16)
    (StageGamma.fixedRead_run C NativeRows.fieldWidth value (by decide) (by decide) a hc
      Lin (SInt.encS t) rest hfield hfieldWidth hin)
    (fun b ⟨hbv, _, hbip, hbrest, hbc, hbfr⟩ => ?_)) (by omega) (fun _ h => h)
  have hbp : b.env positive = a.env positive := hbfr _ (by decide)
  have hbn : b.env negative = a.env negative := hbfr _ (by decide)
  refine Hs.mono (finalizeTargetProgram_run C b hbc t
    (by simpa only [Nat.mod_eq_of_lt ht] using hbv) hwidth
    (by rw [hbp, hbn]; exact hfit)) le_rfl ?_
  rintro c ⟨hcv, hcm, hcsh, hcc, hcf⟩
  have hs := Same.of_sh hcsh
  refine ⟨by simpa only [hbp, hbn] using hcv, by simpa only [hbp, hbn] using hcm,
    hs.ip.trans hbip, ?_, ?_, ?_, hcc, ?_⟩
  · exact hs.out.trans (congrArg Prod.fst hbrest)
  · exact hs.ram.trans (congrArg (fun v => v.2.1) hbrest)
  · exact hs.rc.trans (congrArg (fun v => v.2.2.1) hbrest)
  · exact (hbfr.weaken (by intro y hy; exact List.mem_append_left _ hy)).trans
      (hcf.weaken (by intro y hy; exact List.mem_append_right _ hy))

/-- `imp:pullback`, paper/paper.tex: the original
target field physically produces its exact adjusted signed encoding. -/
theorem originalTargetProgram_run (C : Ctx) (a : DS VV MM) (hc : Cst a) (t : ℤ)
    (Lin : ℕ) (rest : List Bool) (hwidth : 2 ≤ C.Wd)
    (hfield : a.env NativeRows.fieldWidth = Lin) (hfieldWidth : Lin + 1 ≤ C.Wd)
    (ht : SInt.encS t < 2 ^ Lin)
    (hin : C.inp.drop a.ip = binary Lin (SInt.encS t) ++ rest)
    (hfit : 2 * (a.env positive + a.env negative + t.natAbs) + 1 < 2 ^ C.Wd) :
    Hs C originalTargetProgram a (10 * Lin + 40) (fun b =>
      b.env value = SInt.encS ((a.env positive : ℤ) - a.env negative + t) ∧
      b.env positive + b.env negative = a.env positive + a.env negative + t.natAbs ∧
      b.ip = a.ip + Lin ∧ b.out = a.out ∧ b.ram = a.ram ∧ b.rc = a.rc ∧ Cst b) :=
  Hs.mono (originalTargetProgram_run_frame C a hc t Lin rest hwidth hfield hfieldWidth ht hin hfit)
    le_rfl (fun _ ⟨hv, hm, hi, ho, hr, hrc, hc, _⟩ => ⟨hv, hm, hi, ho, hr, hrc, hc⟩)

end NearQuarticWires.StagePullback.SignedCoefficients
