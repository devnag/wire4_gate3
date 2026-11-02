import Proof.Quartic.StageCert.BinomialLoop

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicGates.Close.Cells

/-- `lem:maskpoly`, paper/paper.tex: the exact binary
binomial recurrence has a constant-cost zero-index initialization. -/
theorem binomialStart_run (C : Ctx) (a : DS VV MM) (hc : Cst a) :
    Hs C binomialStart a 3 (fun z=>z.env chooseValue=1 ∧ z.env chooseI=0 ∧
      z.sh=a.sh ∧ Cst z ∧ Fr a z [chooseI,chooseValue]) := by
  unfold binomialStart
  refine Hs.seq (t1 := 1) (t2 := 1) (hs_copy C chooseValue v1 a (by decide)) ?_
  rintro b rfl
  refine (hs_zero C chooseI _).mono le_rfl ?_
  rintro z rfl
  refine ⟨by vsimp [chooseI,chooseValue,hc.one],by simp,rfl,?_,
    (Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp))⟩
  exact ⟨by vsimp [chooseI,chooseValue,hc.z],by vsimp [chooseI,chooseValue,hc.one],
    by vsimp [chooseI,chooseValue,hc.two]⟩

/-- `lem:maskpoly` and `prop:time`, paper/paper.tex: initialization and all exact natural divisions are charged
in one complete original binary binomial procedure. -/
theorem binomialProgram_run (C : Ctx) (a : DS VV MM) (hc : Cst a) (n r : ℕ)
    (hn : a.env chooseN=n) (hr : a.env chooseR=r) (hrn : r≤n)
    (hfit : 2^n*(n+1)<2^C.Wd) (hsmall : 2*(n+1)≤2^C.Wd) :
    Hs C binomialProgram a (17*r+6) (fun z=>z.env chooseValue=n.choose r ∧
      z.env chooseI=r ∧ z.sh=a.sh ∧ Cst z ∧ Fr a z binomialScratch) := by
  unfold binomialProgram
  refine (Hs.seq (t1 := 3) (t2 := 17*r+2) (binomialStart_run C a hc) ?_).mono
    (by omega) (fun _ h=>h)
  rintro b ⟨bv,bi,bsh,bc,bfr⟩
  refine (binomialLoop_run C b bc n r ((bfr _ (by decide)).trans hn)
    ((bfr _ (by decide)).trans hr) bi bv hrn hfit hsmall).mono le_rfl ?_
  rintro z ⟨zv,zi,zsh,zc,zfr⟩
  exact ⟨zv,zi,zsh.trans bsh,zc,(bfr.weaken (by decide)).trans zfr⟩

/-- `lem:maskpoly`, paper/paper.tex: the exact natural
binomial routine includes its vanishing branch when the lower index exceeds
the upper index, before any residue operation. -/
def exactBinomial : St VV MM := .ite (.lt chooseN chooseR) (.op (.zero chooseValue)) binomialProgram

/-- `lem:maskpoly` and `prop:time`, paper/paper.tex: every natural pair has its exact original binomial value
after linearly many binary arithmetic operations in the smaller index. -/
theorem exactBinomial_run (C : Ctx) (a : DS VV MM) (hc : Cst a) (n r : ℕ)
    (hn : a.env chooseN=n) (hr : a.env chooseR=r)
    (hfit : 2^n*(n+1)<2^C.Wd) (hsmall : 2*(n+1)≤2^C.Wd) :
    Hs C exactBinomial a (17*min n r+8) (fun z=>z.env chooseValue=n.choose r ∧
      z.sh=a.sh ∧ Cst z ∧ Fr a z binomialScratch) := by
  unfold exactBinomial
  refine (Hs.ite (t := 17*min n r+7) (c := .lt chooseN chooseR)
    (show chooseN≠chooseR by decide) ?_ ?_).mono (by omega) (fun _ h=>h)
  · intro he
    have hnr : n<r := by simpa only [Cnd.eval,hn,hr,decide_eq_true_eq] using he
    refine (hs_zero C chooseValue a).mono (by omega) ?_
    rintro z rfl
    refine ⟨by simp [Nat.choose_eq_zero_of_lt hnr],rfl,?_,Fr.set _ _ (by simp [binomialScratch])⟩
    exact Cst.of_fr hc (Fr.set (T := [chooseValue]) _ _ (by simp)) (by decide)
  · intro he
    have hrn : r≤n := by simpa only [Cnd.eval,hn,hr,decide_eq_false_iff_not,not_lt] using he
    refine (binomialProgram_run C a hc n r hn hr hrn hfit hsmall).mono
      (by rw [min_eq_right hrn]; omega) ?_
    rintro z ⟨zv,_zi,zsh,zc,zfr⟩
    exact ⟨zv,zsh,zc,zfr⟩

end NearQuarticWires.StageCert.Tokens
