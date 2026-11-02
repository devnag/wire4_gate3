import Proof.Quartic.StageCert.BinomialAdvance

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicGates.Close.Cells

/-- `lem:maskpoly`, paper/paper.tex: a complete exact
binary binomial recurrence first multiplies, then divides in the naturals. -/
def binomialStep : St VV MM :=
  .seq binomialFactor (.seq binomialDenominator binomialAdvance)

/-- `lem:maskpoly`, paper/paper.tex: the exact binary
binomial routine changes only its seven explicit recurrence fields. -/
def binomialScratch : List (Fin VV) :=
  [chooseI,chooseValue,chooseFactor,chooseProduct,chooseDenominator,chooseQuotient,chooseRemainder]

/-- `lem:maskpoly` and `prop:time`, paper/paper.tex: exact binomial progression has constant operation count
and polynomial binary capacity, independently of the coefficient's value. -/
theorem binomialStep_run (C : Ctx) (a : DS VV MM) (hc : Cst a) (n i : ℕ)
    (hn : a.env chooseN=n) (hi : a.env chooseI=i) (hv : a.env chooseValue=n.choose i)
    (hin : i<n) (hfit : 2^n*(n+1)<2^C.Wd) (hsmall : 2*(n+1)≤2^C.Wd) :
    Hs C binomialStep a 15 (fun z=>z.env chooseValue=n.choose (i+1) ∧
      z.env chooseI=i+1 ∧ z.env chooseRemainder=0 ∧ z.sh=a.sh ∧ Cst z ∧ Fr a z binomialScratch) := by
  unfold binomialStep
  refine Hs.seq (t1 := 5) (t2 := 9) (binomialFactor_run C a hc n i hn hi hv hin.le hfit) ?_
  rintro b ⟨_bf,bp,bsh,bc,bfr⟩
  have bi : b.env chooseI=i := (bfr _ (by decide)).trans hi
  refine Hs.seq (t1 := 3) (t2 := 5) (binomialDenominator_run C b bc i bi (by omega)) ?_
  rintro d ⟨dd,dsh,dc,dfr⟩
  refine (binomialAdvance_run C d dc n i ((dfr _ (by decide)).trans bi)
    ((dfr _ (by decide)).trans bp) dd (by omega)).mono le_rfl ?_
  rintro z ⟨zv,zi,zr,zsh,zc,zfr⟩
  exact ⟨zv,zi,zr,zsh.trans (dsh.trans bsh),zc,
    (bfr.weaken (by decide)).trans ((dfr.weaken (by decide)).trans (zfr.weaken (by decide)))⟩

end NearQuarticWires.StageCert.Tokens
