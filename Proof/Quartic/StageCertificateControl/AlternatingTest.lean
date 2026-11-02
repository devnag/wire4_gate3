import Proof.Quartic.StageCertificateControl.InputTest

/-!
# Alternating complete bitmap stores

Paper: Step 2 of `sec:algorithm`, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open NearCubicGates.Close.WordPrograms.SInt (encS)
open NearCubicGates.Close.CounterMachine.CellTables (u4)
open StageRecovery (countVar widthVar magnitudeVar signVar)
open StageCertTests (flagVar thresholdVar updatedFlagList)

/-- Step 2 of `sec:algorithm`, paper/paper.tex:
the active bitmap selector is retained outside both table parsers. -/
def modeVar : Fin VV := ⟨122,by decide⟩

/-- The two retained arrays of `sec:algorithm`, paper/paper.tex, alternate without a third bitmap or a prefix crop. -/
def activeStore (first second : Fin MM) (mode : Bool) : Fin MM :=
  if mode then second else first

/-- Step 2 of `sec:algorithm`, paper/paper.tex:
one whole test writes the other complete array and changes the selector. -/
def alternatingTest (first second : Fin MM) : St VV MM :=
  .ite (.eq modeVar vZ)
    (.seq (inputTest first second) (.op (.copy modeVar v1)))
    (.seq (inputTest second first) (.op (.zero modeVar)))

/-- The whole signed test of `sec:algorithm` and `prop:time`,
paper/paper.tex, updates exactly
the alternate array. Its selector is an actual retained register,
and both full-size arrays remain available for subsequent tests. -/
theorem alternatingTest_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (first second : Fin MM) (hstores : first≠second)
    (mode : Bool) (hmode : a.env modeVar=mode.toNat)
    (test : NativeTest) (flags : List Bool) (rest : List Bool)
    (hl : flags.length=test.values.length)
    (hin : C.inp.drop a.ip=test.word++rest)
    (hcount : a.env countVar=test.values.length) (hcountfit : test.values.length<2^C.Wd)
    (hvalues : ∀ z∈test.values, encS z<2^test.width)
    (hwidth : test.width+2≤C.Wd)
    (hboundWord : natBitLength test.bound+2≤C.Wd)
    (hwidthWord : natBitLength test.width+2≤C.Wd) (hfour : 4≤2^C.Wd)
    (hflags : a.ram (activeStore first second mode)=flags.map Bool.toNat)
    (houtput : (a.ram (activeStore first second (!mode))).length=test.values.length)
    (hri : a.rc first=test.values.length) (hro : a.rc second=test.values.length) :
    Hs C (alternatingTest first second) a (test.sourceCost+3) (fun b =>
      b.env modeVar=(!mode).toNat ∧
      b.ram=Function.update a.ram (activeStore first second (!mode))
        ((updatedFlagList test.bound flags test.values).map Bool.toNat) ∧
      b.rc=a.rc ∧ b.ip=a.ip+test.word.length ∧ C.inp.drop b.ip=rest ∧
      (b.out,b.kin,b.kout,b.kc)=(a.out,a.kin,a.kout,a.kc) ∧ Cst b ∧
      Fr a b (modeVar::([thresholdVar,widthVar,c0,t0,t1,t3,u4,flagVar,magnitudeVar,signVar,vJ]++rdNatT))) := by
  cases mode with
  | false =>
    simp only [activeStore,Bool.not_false,Bool.not_true,Bool.false_eq_true,ite_false,ite_true] at hflags houtput ⊢
    unfold alternatingTest
    refine Hs.iteT (show modeVar≠vZ by decide) (by simp [Cnd.eval,hmode,hc.z]) ?_
    refine Hs.seq (t2 := 1)
      (inputTest_spec C a hc first second (hstores) test flags rest hl hin
        hcount hcountfit hvalues hwidth hboundWord hwidthWord hfour hflags houtput hri hro)
      fun b ⟨hbr,hbc,hbi,hbin,hbs,hcc,hbf⟩ => ?_
    refine (hs_copy C modeVar v1 b (by decide)).mono le_rfl ?_
    rintro d rfl
    refine ⟨?_,hbr,hbc,hbi,hbin,hbs,?_,?_⟩
    · simpa only [DS.set_env_self,Bool.toNat_true] using hcc.one
    · exact Cst.of_fr (T := [modeVar]) hcc (Fr.set _ _ (by decide)) (by decide)
    · exact Fr.trans (Fr.weaken hbf (by intro y hy;exact List.mem_cons_of_mem _ hy))
        (Fr.set _ _ (by simp))
  | true =>
    simp only [activeStore,Bool.not_false,Bool.not_true,Bool.false_eq_true,ite_false,ite_true] at hflags houtput ⊢
    unfold alternatingTest
    refine Hs.iteF (show modeVar≠vZ by decide) (by simp [Cnd.eval,hmode,hc.z]) ?_
    refine Hs.seq (t2 := 1)
      (inputTest_spec C a hc second first (Ne.symm hstores) test flags rest hl hin
        hcount hcountfit hvalues hwidth hboundWord hwidthWord hfour hflags houtput hro hri)
      fun b ⟨hbr,hbc,hbi,hbin,hbs,hcc,hbf⟩ => ?_
    refine (hs_zero C modeVar b).mono le_rfl ?_
    rintro d rfl
    refine ⟨by simp,hbr,hbc,hbi,hbin,hbs,?_,?_⟩
    · exact Cst.of_fr (T := [modeVar]) hcc (Fr.set _ _ (by decide)) (by decide)
    · exact Fr.trans (Fr.weaken hbf (by intro y hy;exact List.mem_cons_of_mem _ hy))
        (Fr.set _ _ (by simp))

end NearQuarticWires.StageCertificateControl
