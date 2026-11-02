import Proof.Quartic.StageModularSetup.Modulus
import Proof.Quartic.StageModularSetup.ZeroBank
import Proof.Quartic.StageModularSetup.Bounds

set_option autoImplicit false

namespace NearQuarticWires.StageModularSetup

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms
open StageModularCuts StageModularCuts.Setup

/-- `lem:print`, paper/paper.tex: the complete
loaded setup derives dimensions, initializes the binary modulus, and
writes every arithmetic zero word from the retained bounded width. -/
def initializeLoaded : StageModularCuts.Program :=
  .seq initializeWidths
    (.seq (.wm initializeModulus) (.wm (initializeZeroWords [6,8,9,10,11])))

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual literal-source initialization reaches the
exact frozen ready state, including all unrelated tapes and cleared scratch. -/
theorem initializeLoaded_spec (r : Request) :
    WXExec (capacity r) initializeLoaded (loaded r) (ready r)
      (100*(r.width+r.fieldWidth+1)+500*(r.fieldWidth+2)+
        5*(60*(r.fieldWidth+1)+41)+2) := by
  have hcap:=setup_counter_capacity r
  have hd : r.width+r.fieldWidth+2≤ scale r := by unfold scale;omega
  have eWidth:=initializeWidths_spec (capacity r) r (by omega)
  let a:=((loaded r).setv 7 (r.fieldWidth+1)).setv 8 (2*r.width+1)
  have eMod:=initializeModulus_spec (capacity r) (r.fieldWidth+1) r.modulus a
    rfl rfl rfl rfl (by simp [a])
    (by simp [a,loaded]) (by simp [a,loaded]) (by simp [a,loaded])
    (by simp [a,loaded]) (by simp [a,loaded]) (by simp [a,loaded])
    (by simp [a,loaded]) (modulus_length_bound r) (by omega)
  let b:=a.sets 7 (frame (binary (r.fieldWidth+1) r.modulus))
  have eZero:=initializeZeroWords_spec (capacity r) (r.fieldWidth+1)
    [6,8,9,10,11] (by decide) b
    (by intro output ht;simp at ht;rcases ht with h|h|h|h|h <;> subst output <;> rfl)
    (by intro output ht;rfl)
    (by simp [b,a]) (by simp [b,a,loaded]) (by simp [b,a,loaded])
    (by simp [b,a,loaded]) (by omega)
  refine (eWidth.seq ((WXExec.wm eMod).seq (WXExec.wm eZero))).cast (capacity r) ?_ ?_
  · apply WState.eq
    · rfl
    · funext stream
      fin_cases stream <;>
        simp [List.foldl_cons,List.foldl_nil,b,a,ready,
          coefficient,modulus,magnitude,quotient,remainder,temporary]
    · rfl
    · rfl
  · norm_num only [List.length_cons,List.length_nil]
    omega

end NearQuarticWires.StageModularSetup
