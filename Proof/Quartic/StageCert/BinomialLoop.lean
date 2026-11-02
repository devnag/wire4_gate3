import Proof.Quartic.StageCert.BinomialStep

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicGates.Close.Cells

/-- `lem:maskpoly`, paper/paper.tex: the exact binary
coefficient routine starts with `choose(n,0)=1`. -/
def binomialStart : St VV MM :=
  .seq (.op (.copy chooseValue v1)) (.op (.zero chooseI))

/-- `lem:maskpoly`, paper/paper.tex: the lower argument
controls the complete finite exact binomial recurrence. -/
def binomialLoop : St VV MM := .loop (.lt chooseI chooseR) binomialStep

/-- `lem:maskpoly`, paper/paper.tex: all original
binary binomial work, including initialization, is one concrete program. -/
def binomialProgram : St VV MM := .seq binomialStart binomialLoop

/-- `lem:maskpoly` and `prop:time`, paper/paper.tex: exact binomial coefficients require linearly many bounded
binary arithmetic operations, with no unary loop over their magnitudes. -/
theorem binomialLoop_run (C : Ctx) (a : DS VV MM) (hc : Cst a) (n r : ℕ)
    (hn : a.env chooseN=n) (hr : a.env chooseR=r) (hi : a.env chooseI=0)
    (hv : a.env chooseValue=1) (hrn : r≤n)
    (hfit : 2^n*(n+1)<2^C.Wd) (hsmall : 2*(n+1)≤2^C.Wd) :
    Hs C binomialLoop a (17*r+2) (fun z=>z.env chooseValue=n.choose r ∧
      z.env chooseI=r ∧ z.sh=a.sh ∧ Cst z ∧ Fr a z binomialScratch) := by
  let I : ℕ→DS VV MM→Prop := fun i b=>
    b.env chooseValue=n.choose i ∧ b.env chooseI=i ∧ b.env chooseN=n ∧ b.env chooseR=r ∧
    b.sh=a.sh ∧ Cst b ∧ Fr a b binomialScratch
  have step : ∀i<r,∀b,I i b→Cnd.eval b (.lt chooseI chooseR)=true ∧
      Hs C binomialStep b 15 (I (i+1)) := by
    intro i hir b ⟨bv,bi,bn,br,bsh,bc,bfr⟩
    refine ⟨by simp [Cnd.eval,bi,br,hir],?_⟩
    refine (binomialStep_run C b bc n i bn bi bv (by omega) hfit hsmall).mono le_rfl ?_
    rintro z ⟨zv,zi,_zr,zsh,zc,zfr⟩
    exact ⟨zv,zi,(zfr _ (by decide)).trans bn,(zfr _ (by decide)).trans br,
      zsh.trans bsh,zc,bfr.trans zfr⟩
  have stop : ∀b,I r b→Cnd.eval b (.lt chooseI chooseR)=false := by
    rintro b ⟨_,bi,_,br,_⟩
    simp [Cnd.eval,bi,br]
  refine (Hs.loopN (C := C) (c := .lt chooseI chooseR) (s := binomialStep)
    (show chooseI≠chooseR by decide) I r 15 step stop a
    ⟨by simpa using hv,hi,hn,hr,rfl,hc,Fr.refl _ _⟩).mono (by omega) ?_
  rintro z ⟨zv,zi,_,_,zsh,zc,zfr⟩
  exact ⟨zv,zi,zsh,zc,zfr⟩

end NearQuarticWires.StageCert.Tokens
