import Proof.Quartic.StageTupleSetupCold.SmallStages

set_option autoImplicit false

namespace NearQuarticWires.StageTupleSetupCold

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.Interfaces
open StageTuple

namespace Helpers

def coefficientValue (one : Bool) : ℤ :=if one then 1 else 0

def coefficientBank (F : Helpers) (one : Bool) :
    Fin F.coefficient.program.tapeCount→Fin (F.ns+1) :=
  if one then F.oneBank else F.zeroBank

def coefficientPair (F : Helpers) (one : Bool) : Fin 2↪Fin (F.ns+1) :=
  if one then F.onePair else F.zeroPair

def coefficientRuler (F : Helpers) (one : Bool) : Fin (F.ns+1) :=F.data (if one then 23 else 22)

/-- `lem:print`, paper/paper.tex: each
coefficient call uses an injective private physical tape bank. -/
theorem coefficientBank_injective (F : Helpers) (one : Bool) :
    Function.Injective (F.coefficientBank one) := by
  cases one
  · exact StageTupleSetup.BankLayout.zeroBank_injective
  · exact StageTupleSetup.BankLayout.twoBank_injective

/-- `lem:print`, paper/paper.tex: both
coefficient banks are disjoint from all retained sources and rulers. -/
theorem coefficientBank_ne_data (F : Helpers) (one : Bool)
    (i : Fin F.coefficient.program.tapeCount) (j : Fin 24) :
    F.coefficientBank one i≠F.data j := by
  cases one
  · exact StageTupleSetup.BankLayout.zeroBank_ne_data i j
  · exact StageTupleSetup.BankLayout.twoBank_ne_data i j

/-- `lem:print`, paper/paper.tex: each
fixed coefficient gets a physically constructed small request from
the genuine width reply and a distinct one-shot ordinary bank. -/
noncomputable def coefficientStage (F : Helpers) (one : Bool) : WMX F.ns 8 :=
  .seq (.wm (StageTupleSetup.coefficientInputProgram (F.coefficientPair one)
    (regs 2 (by decide)) (coefficientValue one)))
    (.machZ F.coefficient.program.machine (F.coefficientBank one) (F.coefficientRuler one))

/-- `lem:print` and `prop:time`, paper/paper.tex: physical small-packet construction
and one ordinary execution produce the exact signed coefficient field. -/
theorem coefficientStage_run (F : Helpers) (one : Bool) (cap : ℕ) (r : TermCutRequest)
    (σ : WState F.ns 8)
    (hs : σ.st (F.widthBank F.width.program.outputTape)=frame (natWord (r.stackWidth+1)))
    (hcold : ∀j,σ.st (F.coefficientBank one j)=[])
    (hh : ∀i,σ.sh i=0) (hz : ∀i,σ.val i=0)
    (hpad : σ.st (F.coefficientRuler one)=
      List.replicate (F.coefficientBudget (CoefficientRequest.mk (r.stackWidth+1) (coefficientValue one))) false)
    (hcap : 2*(natWord (r.stackWidth+1)++intWord (coefficientValue one)).length+10≤cap) :
    ∃τ tout,WXExec cap (F.coefficientStage one) σ τ
      (1000*((natWord (r.stackWidth+1)++intWord (coefficientValue one)).length+1)+1+
        (2*F.coefficientBudget (CoefficientRequest.mk (r.stackWidth+1) (coefficientValue one))+2)) ∧
      Docked (F.coefficientBank one) σ τ (fun _=>0) tout ∧
      τ.st (F.coefficientBank one F.coefficient.program.outputTape)=
        (CoefficientRequest.mk (r.stackWidth+1) (coefficientValue one)).output := by
  have hp0 : F.coefficientPair one 0=F.widthBank F.width.program.outputTape := by cases one <;> rfl
  have hp1 : F.coefficientPair one 1=F.coefficientBank one F.coefficientInput := by cases one <;> rfl
  have he:=StageTupleSetup.coefficientInputProgram_spec cap (F.coefficientPair one)
    (regs 2 (by decide)) (r.stackWidth+1) (coefficientValue one) σ
    (by rw [hp0];exact hs) (hh _) (by rw [hp1];exact hcold _) (hh _) (fun i=>hz _) hcap
  rw [hp1] at he
  exact call_after_input F.coefficient (CoefficientRequest.mk (r.stackWidth+1) (coefficientValue one))
    cap (F.coefficientBank one) (F.coefficientBank_injective one) F.coefficientInput rfl
    (F.coefficientRuler one) (fun j=>F.coefficientBank_ne_data one j _)
    _ _ σ he hcold (fun j=>hh _) hpad (hh _)

end Helpers

end NearQuarticWires.StageTupleSetupCold
