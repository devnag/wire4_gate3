import Proof.Quartic.StageTupleSetupCold.SourceLoad
import Proof.Quartic.StageTupleSetup.BankSeparation
import Proof.Quartic.StageTupleSetup.PreparedContract

set_option autoImplicit false

namespace NearQuarticWires.StageTupleSetupCold

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Interfaces
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open StageTuple

/-- `lem:print`, paper/paper.tex: three
actual small-helper programs supply the width, row count and both
fixed coefficients. Private tape counts remain abstract during the
physical composition; no complete Terms packet is an arithmetic input. -/
structure Helpers where
  widthBudget : ℕ→ℕ
  width : WordFunction ℕ natWord (fun W=>frame (natWord (W+1))) widthBudget
  rowBudget : StageNativeRowCount.Request→ℕ
  row : WordFunction StageNativeRowCount.Request StageNativeRowCount.Request.word
    StageNativeRowCount.Request.output rowBudget
  coefficientBudget : CoefficientRequest→ℕ
  coefficient : WordFunction CoefficientRequest CoefficientRequest.word
    CoefficientRequest.output coefficientBudget

namespace Helpers

def ns (F : Helpers) : ℕ :=StageTupleSetup.BankLayout.setupNS
  F.width.program.tapeCount F.row.program.tapeCount F.coefficient.program.tapeCount

def data (F : Helpers) (i : Fin 24) : Fin (F.ns+1) :=
  StageTupleSetup.BankLayout.dataTape i

def loader (F : Helpers) (i : Fin 14) : Fin (F.ns+1) :=
  StageTupleSetup.BankLayout.loaderBank i

def widthBank (F : Helpers) (i : Fin F.width.program.tapeCount) : Fin (F.ns+1) :=
  StageTupleSetup.BankLayout.widthBank i

def rowBank (F : Helpers) (i : Fin F.row.program.tapeCount) : Fin (F.ns+1) :=
  StageTupleSetup.BankLayout.rowBank i

def zeroBank (F : Helpers) (i : Fin F.coefficient.program.tapeCount) : Fin (F.ns+1) :=
  StageTupleSetup.BankLayout.zeroBank i

def oneBank (F : Helpers) (i : Fin F.coefficient.program.tapeCount) : Fin (F.ns+1) :=
  StageTupleSetup.BankLayout.twoBank i

def widthInput (F : Helpers) : Fin F.width.program.tapeCount :=⟨0,by
  have h:=F.width.program.twoTapes
  omega⟩

def rowInput (F : Helpers) : Fin F.row.program.tapeCount :=⟨0,by
  have h:=F.row.program.twoTapes
  omega⟩

def coefficientInput (F : Helpers) : Fin F.coefficient.program.tapeCount :=⟨0,by
  have h:=F.coefficient.program.twoTapes
  omega⟩

end Helpers

/-- `lem:print`, paper/paper.tex: a
source/cache pair consists of physically distinct retained tapes. -/
def pair {ns : ℕ} (src dst : Fin (ns+1)) (h : src≠dst) : Fin 2↪Fin (ns+1) :=
  ⟨![src,dst],by
    intro i j he
    fin_cases i <;> fin_cases j
    · rfl
    · exact False.elim (h he)
    · exact False.elim (h he.symm)
    · rfl⟩

/-- `lem:print`, paper/paper.tex: the
fixed scratch registers contain no data-dependent allocator or cache. -/
def regs (m : ℕ) (h : m≤8) : Fin m↪Fin 8 :=
  ⟨fun i=>⟨i.val,by have hi:=i.isLt;omega⟩,fun i j he=>
    Fin.ext (show i.val=j.val from congrArg (fun z : Fin 8=>z.val) he)⟩

namespace Helpers

def widthPair (F : Helpers) : Fin 2↪Fin (F.ns+1) :=
  pair (F.data 6) (F.widthBank F.widthInput) (by
    exact (StageTupleSetup.BankLayout.widthBank_ne_data F.widthInput 6).symm)

def contextPair (F : Helpers) : Fin 2↪Fin (F.ns+1) :=
  StageTupleSetup.BankLayout.contextPair

def degreePair (F : Helpers) : Fin 2↪Fin (F.ns+1) :=
  pair (F.data 7) (F.data 15) (by
    intro h
    have hh:=congrArg Fin.val h
    norm_num [data,StageTupleSetup.BankLayout.dataTape] at hh)

def rowPair (F : Helpers) : Fin 2↪Fin (F.ns+1) :=
  pair (F.data 3) (F.rowBank F.rowInput) (by
    exact (StageTupleSetup.BankLayout.rowBank_ne_data F.rowInput 3).symm)

def zeroPair (F : Helpers) : Fin 2↪Fin (F.ns+1) :=
  pair (F.widthBank F.width.program.outputTape) (F.zeroBank F.coefficientInput)
    (StageTupleSetup.BankLayout.width_zero_ne _ _)

def onePair (F : Helpers) : Fin 2↪Fin (F.ns+1) :=
  pair (F.widthBank F.width.program.outputTape) (F.oneBank F.coefficientInput)
    (StageTupleSetup.BankLayout.width_two_ne _ _)

/-- `lem:print`, paper/paper.tex: the
prepared formatter's ten ports refer only to original retained sources,
genuine helper replies and one fresh final output. -/
def preparedTape (F : Helpers) (i : Fin 10) : Fin (F.ns+1) :=
  ![F.data 2,F.data 3,F.data 14,F.data 1,
    F.widthBank F.width.program.outputTape,
    F.zeroBank F.coefficient.program.outputTape,
    F.oneBank F.coefficient.program.outputTape,
    F.rowBank F.row.program.outputTape,F.data 15,F.data 16] i

/-- `lem:print`, paper/paper.tex: every
prepared-input source and the fresh output have distinct physical ports. -/
theorem preparedTape_injective (F : Helpers) : Function.Injective F.preparedTape := by
  intro i j he
  have hw:=F.width.program.outputTape.isLt
  have hr:=F.row.program.outputTape.isLt
  have hc:=F.coefficient.program.outputTape.isLt
  have hh:=congrArg Fin.val he
  fin_cases i <;> fin_cases j <;>
    simp [preparedTape,data,widthBank,rowBank,zeroBank,oneBank,
      StageTupleSetup.BankLayout.dataTape,StageTupleSetup.BankLayout.widthBank,
      StageTupleSetup.BankLayout.rowBank,StageTupleSetup.BankLayout.zeroBank,
      StageTupleSetup.BankLayout.twoBank] at hh ⊢ <;> omega

def preparedPorts (F : Helpers) : Fin 10↪Fin (F.ns+1) :=⟨F.preparedTape,F.preparedTape_injective⟩

end Helpers

end NearQuarticWires.StageTupleSetupCold
