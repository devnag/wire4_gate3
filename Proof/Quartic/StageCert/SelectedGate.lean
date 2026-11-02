import Proof.Quartic.StageCert.SelectedMagnitude

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicWires
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces
open NearQuarticWires.StageMain

/-- `sec:cells`, paper/paper.tex: the four-bit signed
mixed difference always lies in the unconditional integer range `[-2,2]`. -/
theorem fourBitDifference_natAbs_le_two (f : Fin 4→Bool) :
    (fourBitDifference f).natAbs≤2 := by
  cases h0 : f 0 <;> cases h1 : f 1 <;> cases h2 : f 2 <;> cases h3 : f 3 <;>
    norm_num [fourBitDifference,h0,h1,h2,h3,NearCubicWires.WireExponent3_5.Shared.bitZ]

/-- `def:mask`, paper/paper.tex: one original gate is
evaluated and its magnitude added precisely when its retained W2 bit is set. -/
def selectedGate : St VV := .seq deltaGate addSelectedMagnitude

/-- `def:mask`, paper/paper.tex: the selected source
population accumulator is additional to the mixed-difference workspace. -/
def selectedGateScratch : List (Fin VV) := populationTotal::deltaGateScratch

/-- `sec:cells`, `def:mask` and `prop:time`, paper/paper.tex: the original occurrence's selected
population contribution is accumulated by exact source-word evaluation. -/
theorem selectedGate_run (C : Ctx) {n : ℕ} (g : NormalizedThresholdGate n)
    (a : DS VV) (hc : Cst a) (rest : List Bool)
    (hin : C.cw.drop a.cp=gateWord g++rest) (hbase : a.cp≤C.cw.length)
    (hW : C.cw.length+3≤C.Wd) (hpoint : ∀l,a.env (cornerPoint l)<2^C.Wd)
    (selected : Bool) (hselected : a.env sourceWitnessResult=selected.toNat)
    (hfit : a.env populationTotal+2<2^C.Wd) :
    Hs C selectedGate a (860*(C.cw.length+2)^2+53) (fun z =>
      z.env populationTotal=a.env populationTotal+
        (if selected then
          (fourBitDifference (fun l=>g.eval (packedPoint n (a.env (cornerPoint l))))).natAbs
        else 0) ∧
      z.cp=a.cp+(gateWord g).length ∧ z.wq=a.wq ∧ z.out=a.out ∧ Cst z ∧
      FrS a z selectedGateScratch) := by
  unfold selectedGate
  refine Hs.seq (t1 := 860*(C.cw.length+2)^2+50) (t2 := 2)
    (deltaGate_run C g a hc rest hin hbase hW hpoint) ?_
  rintro b ⟨_bp,_bn,bm,bc,bw,bo,bconst,bfr⟩
  have bs : b.env sourceWitnessResult=selected.toNat :=
    (bfr _ (by decide) (by decide)).trans hselected
  have bt : b.env populationTotal=a.env populationTotal := bfr _ (by decide) (by decide)
  have bfit : b.env populationTotal+b.env deltaMagnitude<2^C.Wd := by
    rw [bt,bm]
    have h := fourBitDifference_natAbs_le_two (fun l=>g.eval (packedPoint n (a.env (cornerPoint l))))
    omega
  refine (addSelectedMagnitude_run C b bconst selected bs bfit).mono le_rfl ?_
  rintro z ⟨zt,zc,zw,zo,zconst,zfr⟩
  refine ⟨by simpa only [bt,bm] using zt,zc.trans bc,zw.trans bw,zo.trans bo,zconst,?_⟩
  exact (bfr.weaken (by decide)).trans (zfr.toS.weaken (by decide))

end NearQuarticWires.StageCert
