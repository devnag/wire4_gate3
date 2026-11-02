import Proof.Quartic.StagePrint.HeaderWidthProgram
import Proof.Quartic.StagePrint.DenseWidth
import Proof.Quartic.StageFormulaMetadata.NaturalLength
import Proof.Quartic.StagePrint.GreedyEntryData

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.GreedyEntry

open NearCubicWires NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: retained binary
entry metadata and the constant-size arithmetic registers. -/
def degreeVar : Fin VV := 71
def modulusVar : Fin VV := 72
def coefficientBitsVar : Fin VV := 73
def halfVar : Fin VV := 74
def sumVar : Fin VV := 75
def factorVar : Fin VV := 77
def productVar : Fin VV := 78
def widthVar : Fin VV := 79

def maximumProgram : St VV MM :=
  .ite (.lt productVar coefficientBitsVar) (.op (.copy widthVar coefficientBitsVar)) skipS

/-- `lem:print`, paper/paper.tex: the actual
binary comparison selects a maximum without enumerating either value. -/
theorem maximumProgram_run (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (hw : a.env widthVar=a.env productVar) :
    Hs C maximumProgram a 2 (fun b =>
      b.env widthVar=max (a.env coefficientBitsVar) (a.env productVar) ∧
      b.sh=a.sh ∧ Cst b ∧ Fr a b [widthVar,vJ]) := by
  unfold maximumProgram
  by_cases h : a.env productVar<a.env coefficientBitsVar
  · refine (Hs.iteT (c:=.lt productVar coefficientBitsVar) (show productVar≠coefficientBitsVar by decide)
      (by simpa only [Cnd.eval,decide_eq_true_eq] using h)
      (hs_copy C widthVar coefficientBitsVar a (by decide))).mono le_rfl ?_
    rintro b rfl
    refine ⟨?_,rfl,Cst.of_fr hc (Fr.set a (x:=widthVar) (a.env coefficientBitsVar) (T:=[widthVar,vJ]) (by simp)) (by decide),Fr.set a _ (by simp)⟩
    simpa only [DS.set_env_self] using (max_eq_left (Nat.le_of_lt h)).symm
  · refine (Hs.iteF (c:=.lt productVar coefficientBitsVar) (show productVar≠coefficientBitsVar by decide)
      (by simpa only [Cnd.eval,decide_eq_false_iff_not] using h)
      (skip_spec a)).mono le_rfl ?_
    rintro b rfl
    refine ⟨?_,rfl,Cst.of_fr hc (Fr.set a (x:=vJ) 0 (T:=[widthVar,vJ]) (by simp)) (by decide),Fr.set a _ (by simp)⟩
    simp only [DS.set_env_ne _ _ (show widthVar≠vJ by decide),hw,max_eq_right (by omega : a.env coefficientBitsVar≤a.env productVar)]


end NearQuarticWires.StagePrint.GreedyEntry
