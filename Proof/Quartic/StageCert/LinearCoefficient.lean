import Proof.Quartic.StageCert.ChainRead

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Tabulator

/-- `eq:testE`, `eq:testPhi` and `lem:print`, paper/paper.tex: the nonnegative first summand of an
original proposed-digit or final-error coefficient. -/
def linearPositive : Fin VV := ⟨110,by decide⟩
/-- `eq:testE`, `eq:testPhi` and `lem:print`, paper/paper.tex: the nonnegative subtrahend of the same
complete original integer coefficient. -/
def linearNegative : Fin VV := ⟨111,by decide⟩

/-- `lem:print`(b), paper/paper.tex: the complete
coefficient is a literal integer subtraction, so no signed-normalization
algorithm or loss of a vanishing difference is required. -/
def linearCoefficientFormula {V : ℕ} (positive negative : ℕ) : Formula V :=
  .sub (.const positive) (.const negative)

/-- `lem:print`(b), paper/paper.tex: literal natural
source summands are emitted before their original integer subtraction. -/
def emitLinearCoefficient : St VV MM :=
  .seq (StageLift.emitNaturalConstant linearPositive)
    (.seq (StageLift.emitNaturalConstant linearNegative) (StageLift.emitOperator .sub))

/-- `lem:print` and `prop:time`, paper/paper.tex: exact coefficient generation charges only the actual binary
heights of its nonnegative source summands and retains their signed difference. -/
theorem emitLinearCoefficient_run (C : Ctx) (V positive negative : ℕ)
    (a : DS VV MM) (hc : Cst a) (hp : a.env linearPositive=positive)
    (hn : a.env linearNegative=negative) (hW : 3≤C.Wd)
    (hpf : natBitLength positive+2<2^C.Wd) (hnf : natBitLength negative+2<2^C.Wd) :
    Hs C emitLinearCoefficient a
      (40*natBitLength positive+40*natBitLength negative+129) (fun z=>
      z.out=a.out++(toks (linearCoefficientFormula (V := V) positive negative)).flatMap tokWord ∧
      (z.ip,z.ram,z.rc,z.kin,z.kout,z.kc)=(a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) ∧
      Cst z ∧ Fr a z StageLift.tokenScratch) := by
  unfold emitLinearCoefficient
  apply Hx.hs
  refine Hs.then (StageLift.emitNaturalConstant_spec C linearPositive (by decide) (by decide)
    a hc (by omega) (by rw [hp]; exact hpf))
    (fun b ⟨bo,bs,bc,bfr⟩ n1 hn1=>?_)
  have bn : b.env linearNegative=negative := (bfr _ (by decide)).trans hn
  refine Hs.then (StageLift.emitNaturalConstant_spec C linearNegative (by decide) (by decide)
    b bc (by omega) (by rw [bn]; exact hnf))
    (fun d ⟨doo,ds,dc,dfr⟩ n2 hn2=>?_)
  refine Hs.last (StageLift.emitOperator_spec C .sub d dc)
    (fun z ⟨zo,zs,zc,zfr⟩ n3 hn3=>?_)
  refine ⟨⟨?_,zs.trans (ds.trans bs),zc,bfr.trans (dfr.trans (zfr.weaken (by simp [StageLift.tokenScratch])))⟩,?_⟩
  · rw [zo,doo,bo,hp,bn]
    simp only [linearCoefficientFormula,toks,List.flatMap_append,List.flatMap_cons,
      List.flatMap_nil,List.append_nil,List.append_assoc]
  · have hs : (tokWord .sub).length=7 := by decide
    rw [hp] at hn1
    rw [bn] at hn2
    rw [hs] at hn3
    omega

/-- `lem:print`(b), paper/paper.tex: natural
source summands retain exactly their complete original signed coefficient. -/
theorem linearCoefficientFormula_eval {V : ℕ} (positive negative : ℕ) (point : Fin V→ℤ) :
    (linearCoefficientFormula positive negative).eval point=(positive:ℤ)-negative := rfl

/-- `lem:print` and `prop:time`, paper/paper.tex: native coefficient height is controlled by the original
summands, including complete exact cancellation at zero. -/
theorem linearCoefficientFormula_mass {V : ℕ} (positive negative : ℕ) :
    (linearCoefficientFormula (V := V) positive negative).mass=positive+negative := by
  simp [linearCoefficientFormula,Formula.mass]

end NearQuarticWires.StageCert.Tokens
