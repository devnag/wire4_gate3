import Proof.Quartic.StagePrintTuple.PayloadCopy
import Proof.Gates.Codec.Emit

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.Recovery.HTParts

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: one original
source bit is emitted with two literal marker layers inside a nested
ordinary-machine input field. -/
def emitDoublePair (dst : Fin (ns+1)) (OP : Fin nr) (b : Bool) : WM ns nr :=
  .seq (emitPair dst OP true) (emitPair dst OP b)

/-- `lem:print` and `prop:time`, paper/paper.tex: both marker layers are physically emitted at the same
output cursor, preserving every other tape and register. -/
theorem emits_doublePair (cap : ℕ) (dst : Fin (ns+1)) (OP : Fin nr) :
    Emits cap dst OP (fun b=>marks [true,b]) (emitDoublePair dst OP) 31 := by
  intro b σ ho hc
  have hc4 : σ.val OP+4≤cap := by simpa [marks] using hc
  have e1 := emitPair_spec cap dst OP true σ ho (by omega)
  let d := appendO σ dst OP [true,true]
  have e2 := emitPair_spec cap dst OP b d
    (by simp [d,appendO,ho]) (by simp [d,appendO];omega)
  refine (e1.seq e2).cast cap ?_ (by omega)
  rw [show d=appendO σ dst OP [true,true] from rfl,appendO_append]
  rfl

/-- `lem:print`, paper/paper.tex: the physically
retained framed source is nested as one actual input field, with every
extra marker and its field delimiter written before the source resets. -/
def appendNestedFieldReset (src dst : Fin (ns+1)) (OP SC : Fin nr) : WM ns nr :=
  .seq (CounterAsm.frameCopy src SC (emitDoublePair dst OP))
    (.seq (WM.rewind src SC) (emitPair dst OP false))

/-- `prop:time`, paper/paper.tex: nested-field
construction includes every copied marker, delimiter and source rewind. -/
def appendNestedFieldCost (bits : List Bool) : ℕ := 200*((frame bits).length+1)

/-- `lem:print` and `prop:time`, paper/paper.tex: one real framed source produces exactly the nested
field bytes required inside a framed eleven-field input record. -/
theorem appendNestedFieldReset_spec (cap : ℕ) (src dst : Fin (ns+1)) (OP SC : Fin nr)
    (hsd : src≠dst) (hOS : OP≠SC) (bits rest : List Bool) (σ : WState ns nr)
    (hs : σ.st src=frame bits++rest) (hsh : σ.sh src=0)
    (hd : σ.sh dst=(σ.st dst).length) (hSC : σ.val SC=0)
    (hcap : σ.val OP+4*(frame bits).length+3≤cap) :
    WExec cap (appendNestedFieldReset src dst OP SC) σ
      (appendO σ dst OP (marks (frame (frame bits)))) (appendNestedFieldCost bits) := by
  have e1 := CounterAsm.frameCopy_spec cap hsd hOS (emits_doublePair cap dst OP)
    (d:=4) (by intro b;simp [marks]) bits [] rest σ
    (by simpa using hs) (by simpa using hsh) hd (by omega) (by rw [hSC];omega)
  have hm : (frame bits).flatMap (fun b=>marks [true,b])=marks (marks (frame bits)) := by
    simp only [marks,List.flatMap_assoc]
  rw [hm] at e1
  let d := adv src dst OP SC σ (marks (marks (frame bits))) (frame bits).length
  have hlen : (frame bits).length≤cap := by omega
  have e2 := wrewind_spec cap src SC (frame bits).length d
    (by simp [d,adv,hSC]) (by simpa [d,adv,hSC] using hlen)
  let e := (d.setv SC 0).seth src (d.sh src-(frame bits).length)
  have eh : e=appendO σ dst OP (marks (marks (frame bits))) := by
    apply WState.eq
    · funext i
      by_cases hi : i=src
      · subst hi;simp [e,d,adv,appendO,hsd,hsh]
      · simp [e,d,adv,Function.update_of_ne hi]
    · rfl
    · funext i
      by_cases hi : i=SC
      · subst hi;simp [e,d,adv,appendO,hOS.symm,hSC]
      · simp [e,d,adv,Function.update_of_ne hi]
    · rfl
  have e3 := emitPair_spec cap dst OP false e
    (by rw [eh];simp [appendO,hd])
    (by rw [eh];simp only [appendO_val,Function.update_self,Codec.marks_length];omega)
  refine (e1.seq (e2.seq e3)).cast cap ?_ (by unfold appendNestedFieldCost;omega)
  rw [eh,appendO_append]
  congr 1
  simp only [Codec.frame_eq_marks,Streaming.marks_append,marks,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,List.flatMap_append]

end NearQuarticWires.StageTuple
