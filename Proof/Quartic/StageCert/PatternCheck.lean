import Proof.Quartic.StageCert.PatternVisit

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Incidence
open NearCubicGates.Close.Dispatch
open NearCubicWires NearCubicGates.Close.Interfaces
open NearQuarticWires.StagePrep

/-- `def:mask`, paper/paper.tex: the original occurrence
incidence is extended by zero outside the original coordinate domain. -/
def sourceDegree (c : Call) (j : ℕ) : ℕ :=
  if hj : j<c.n then Cells.incidence (c.first.gates++c.second.gates) ⟨j,hj⟩ else 0

/-- `def:mask`, paper/paper.tex: a zero pattern digit
selects no coordinate; every other digit selects its original block coordinate. -/
def digitNonheavy (c : Call) (cut b block digit : ℕ) : Prop :=
  digit=0 ∨ sourceDegree c (block*b+(digit-1))<cut

instance (c : Call) (cut b block digit : ℕ) :
    Decidable (digitNonheavy c cut b block digit) :=
  inferInstanceAs (Decidable (digit=0 ∨ sourceDegree c (block*b+(digit-1))<cut))

/-- `def:mask`, paper/paper.tex: empty error digits
skip the source scan; nonempty digits run the actual coordinate visit. -/
def checkPatternDigit : St VV := .ite (.eq patternDigit vZ) skipS visitPatternCoordinate

/-- `def:mask` and `prop:time`, paper/paper.tex: checking one decoded digit derives exactly the original
nonheavy-coordinate test from the retained original gate words. -/
theorem checkPatternDigit_run (C : Ctx) (c : Call) (suffix : List Bool)
    (a : DS VV) (hc : Cst a) (P : Prop) [Decidable P]
    (hflag : a.env patternFlag=bnat P)
    (hcoord : a.env patternDigit≠0 →
      a.env patternBlock*a.env patternBlockSize+(a.env patternDigit-1)<c.n)
    (hcw : C.cw=callWord c++suffix) (hW : 2*C.cw.length+8≤C.Wd)
    (hL : 2*C.cw.length+4<2^C.Wd) (hn : c.n<2^C.Wd) :
    Hs C checkPatternDigit a (1203*(C.cw.length+2)^3) (fun b =>
      b.env patternFlag=bnat (P ∧ digitNonheavy c (a.env heavyThreshold)
        (a.env patternBlockSize) (a.env patternBlock) (a.env patternDigit)) ∧
      b.wq=a.wq ∧ b.out=a.out ∧ Cst b ∧ Fr a b patternVisitScratch) := by
  unfold checkPatternDigit
  refine (Hs.ite (t := 1202*(C.cw.length+2)^3) (c := .eq patternDigit vZ)
    (show patternDigit≠vZ by decide) ?_ ?_).mono ?_ (fun _ h => h)
  · intro he
    have hz : a.env patternDigit=0 := by
      simpa only [Cnd.eval,decide_eq_true_eq,hc.z] using he
    refine (skip_spec a).mono (by
      have hp : 0<(C.cw.length+2)^3 := Nat.pow_pos (by omega)
      omega) ?_
    rintro b rfl
    refine ⟨?_,rfl,rfl,?_,Fr.set _ _ (by simp [patternVisitScratch])⟩
    · rw [DS.set_env_ne _ _ (by decide),hflag]
      simp [digitNonheavy,hz]
    · exact Cst.of_fr hc (Fr.set (T := [vJ]) _ _ (by simp)) (by decide)
        (by rw [DS.set_env_ne _ _ (by decide)]; exact hc.pos)
  · intro he
    have hz : a.env patternDigit≠0 := by
      simpa only [Cnd.eval,decide_eq_false_iff_not,hc.z] using he
    have hi := hcoord hz
    refine (visitPatternCoordinate_run C c suffix a hc P hflag (by omega) hi hcw hW hL hn).mono
      le_rfl ?_
    rintro b ⟨bf,_bc,bw,bo,bconst,bfr⟩
    refine ⟨?_,bw,bo,bconst,bfr⟩
    simpa only [digitNonheavy,hz,false_or,sourceDegree,dif_pos hi] using bf
  · have hp : 0<(C.cw.length+2)^3 := Nat.pow_pos (by omega)
    omega

end NearQuarticWires.StageCert.Incidence
