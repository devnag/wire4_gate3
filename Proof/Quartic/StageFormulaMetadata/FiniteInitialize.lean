import Proof.Quartic.StageFormulaMetadata.FiniteSetup

set_option autoImplicit false

namespace NearQuarticWires.StageFormulaMetadata

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.Cells NearCubicGates.Close.WordPrograms

variable {V M : ℕ}

/-- `prop:time`, paper/paper.tex: initialize
the standard cell language from a finite packet whose length is
measured by the actual machine before any binary register is used. -/
def finiteInitialize (K : Callee) : WMX (NS M (TSK K) V) (NR M) :=
  .seq (finiteSetupA K) (.seq (setupB K) (setupC K))

/-- `prop:time`, paper/paper.tex: the complete
measured setup cost charges all zero words, ruler writes and resets. -/
def finiteInitializeCost (variableCount stores len : ℕ) : ℕ :=
  finiteSetupACost len+1+costB variableCount stores (finiteWidth len) 0 0+1+
    costC len (finiteWidth len) 0 0

/-- `prop:time`, paper/paper.tex: measured
allocation establishes the standard representation with no callee
reserve and leaves every input head and scratch register reset. -/
theorem finiteInitialize_spec (K : Callee) (bits : List Bool) (cap : ℕ)
    (hcap : 2*bits.length+8*finiteWidth bits.length+40≤cap) :
    WXExec cap (finiteInitialize (V:=V) (M:=M) K)
      (NearCubicGates.Close.Interfaces.startState (NS M (TSK K) V) (NR M) bits)
      (initSt (t:=TSK K) (finiteWidth bits.length) 0 0 bits)
      (finiteInitializeCost V M bits.length) := by
  have hpos : 0<finiteWidth bits.length := by unfold finiteWidth;omega
  exact (WXExec.seq (finiteSetupA_spec K bits cap (by omega))
    (WXExec.seq (setupB_spec K bits.length (finiteWidth bits.length) 0 0 bits cap (by omega))
      (setupC_spec K bits.length (finiteWidth bits.length) 0 0 bits cap (by omega)))).mono
      (by unfold finiteInitializeCost;omega)

end NearQuarticWires.StageFormulaMetadata
