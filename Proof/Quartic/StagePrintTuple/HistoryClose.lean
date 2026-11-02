import Proof.Quartic.StagePrintTuple.HistoryCursor

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: an appended
Cartesian tuple segment receives its real delimiter, and its actual
emitted-byte count resets the cursor to that segment's first field. -/
def closeRecordHistory (dst : Fin (ns+1)) (OP : Fin nr) : WM ns nr :=
  .seq (emitC dst OP false) (WM.rewind dst OP)

/-- `lem:print`, paper/paper.tex: the exact
history state retains every earlier segment and all newly appended
records while selecting only the new record segment for the next step. -/
def closedHistory (σ : WState ns nr) (dst : Fin (ns+1)) (OP : Fin nr)
    (pre records : List Bool) : WState ns nr :=
  ((σ.sets dst (pre++records++[false])).seth dst pre.length).setv OP 0

/-- `lem:print` and `prop:time`, paper/paper.tex: the next tuple cursor is recovered from the actual
new-output byte counter, with no cumulative-history scan or supplied
output length. Every delimiter write and rewind step is included. -/
theorem closeRecordHistory_spec (cap : ℕ) (dst : Fin (ns+1)) (OP : Fin nr)
    (pre records : List Bool) (σ : WState ns nr)
    (hs : σ.st dst=pre++records) (hh : σ.sh dst=(σ.st dst).length)
    (ho : σ.val OP=records.length) (hcap : records.length+1≤cap) :
    WExec cap (closeRecordHistory dst OP) σ (closedHistory σ dst OP pre records)
      (10*(records.length+1)+10) := by
  have e1 := NearCubicGates.Close.Codec.emitBit_spec cap dst OP false σ hh
    (by rw [ho];omega)
  let a := appendO σ dst OP [false]
  have e2 := wrewind_spec cap dst OP (records.length+1) a
    (by simp [a,appendO,ho]) (by simp only [a,appendO_val,Function.update_self,ho];exact hcap)
  refine (e1.seq e2).cast cap ?_ (by omega)
  apply WState.eq
  · funext i
    by_cases hi:i=dst
    · subst i;simp [a,appendO,closedHistory,hh,hs]
    · simp [a,appendO,closedHistory,Function.update_of_ne hi]
  · simp [a,appendO,closedHistory,hs,List.append_assoc]
  · funext i
    by_cases hi:i=OP
    · subst i;simp [a,appendO,closedHistory]
    · simp [a,appendO,closedHistory,Function.update_of_ne hi]
  · rfl

end NearQuarticWires.StageTuple
