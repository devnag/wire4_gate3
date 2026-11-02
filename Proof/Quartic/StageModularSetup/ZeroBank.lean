import Proof.Quartic.StageModularSetup.ZeroWord

set_option autoImplicit false

namespace NearQuarticWires.StageModularSetup

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open StageModularCuts

/-- `lem:print`, paper/paper.tex: each required
binary arithmetic work tape is physically initialized in fixed order. -/
def initializeZeroWords : List (Fin 16)→WM 15 16
  | []=>.skip
  | output::rest=>.seq (initializeZeroWord output) (initializeZeroWords rest)

/-- `lem:print` and `prop:time`, paper/paper.tex: all work words are actually written from the retained
width, with zero heads and arithmetic scratch preserved between writes. -/
theorem initializeZeroWords_spec (cap width : ℕ) (outputs : List (Fin 16))
    (houtputs : outputs.Nodup) (a : State)
    (hword : ∀ output∈outputs,a.st output=[])
    (hhead : ∀ output∈outputs,a.sh output=0)
    (hwidth : a.val 7=width) (h3 : a.val 3=0) (h4 : a.val 4=0) (h11 : a.val 11=0)
    (hcap : 2*width+1≤cap) :
    WExec cap (initializeZeroWords outputs) a
      (outputs.foldl (fun state output=>state.sets output (frame (binary width 0))) a)
      (outputs.length*(60*width+41)) := by
  induction outputs generalizing a with
  | nil=>simpa only [initializeZeroWords,List.foldl_nil,List.length_nil,Nat.zero_mul] using WExec.skip (cap:=cap) a
  | cons output outputs ih=>
      have hnodup:=List.nodup_cons.mp houtputs
      have eFirst:=initializeZeroWord_spec cap output width a (hword output (by simp))
        (hhead output (by simp)) hwidth h3 h4 h11 hcap
      let b:=a.sets output (frame (binary width 0))
      have eRest:=ih hnodup.2 b
        (by
          intro target ht
          have hne : target≠output := by intro heq;subst heq;exact hnodup.1 ht
          simp only [b,WState.sets_st,Function.update_of_ne hne]
          exact hword target (List.mem_cons_of_mem _ ht))
        (by intro target ht;exact hhead target (List.mem_cons_of_mem _ ht)) hwidth h3 h4 h11
      refine (eFirst.seq eRest).cast cap rfl ?_
      simp only [List.length_cons]
      rw [Nat.add_mul]
      omega

end NearQuarticWires.StageModularSetup
