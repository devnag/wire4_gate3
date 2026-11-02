import Proof.Quartic.StagePrintTuple.NestedField
import Proof.Wire_3_5.PrimAsmCopyNat

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.CopyNat
open NearCubicGates.Close NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.Recovery.HTParts

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: a raw native
field stream is copied into one real Cartesian or Stack input field,
including its record-list delimiter and input-field delimiter. -/
def appendRecordFieldReset (src dst : Fin (ns+1)) (OP SC : Fin nr) : WM ns nr :=
  .seq (CounterAsm.frameLoop src SC (emitDoublePair dst OP))
    (.seq (WM.rewind src SC) (emitWordM dst OP [true,false,false]))

/-- `prop:time`, paper/paper.tex: the actual
raw-field input formatter scans and rewinds its source once. -/
def appendRecordFieldCost (records : List (List Bool)) : ℕ :=
  120*(records.flatMap frame).length+100

/-- `lem:print` and `prop:time`, paper/paper.tex: an actual raw nonempty-field stream, even at a cursor
after a computed count prefix, supplies its exact existing cold-input
record field with every marker and delimiter physically emitted. -/
theorem appendRecordFieldReset_spec (cap : ℕ) (src dst : Fin (ns+1)) (OP SC : Fin nr)
    (hsd : src≠dst) (hOS : OP≠SC) (records : List (List Bool)) (pre rest : List Bool)
    (hne : ∀ record∈records,record≠[]) (hend : rest.headD false=false)
    (σ : WState ns nr) (hs : σ.st src=pre++records.flatMap frame++rest)
    (hsh : σ.sh src=pre.length) (hd : σ.sh dst=(σ.st dst).length)
    (hSC : σ.val SC=0) (hcap : σ.val OP+4*(records.flatMap frame).length+10≤cap) :
    WExec cap (appendRecordFieldReset src dst OP SC) σ
      (appendO σ dst OP (marks (frame (records.flatMap frame++[false]))))
      (appendRecordFieldCost records) := by
  have e1 := CounterAsm.frameLoop_spec cap hsd hOS (emits_doublePair cap dst OP)
    (d:=4) (by intro b;simp [marks]) rest hend records pre σ hne hs hsh hd
    (by omega) (by rw [hSC];omega)
  have hm : (records.flatMap frame).flatMap (fun b=>marks [true,b])=
      marks (marks (records.flatMap frame)) := by
    simp only [marks,List.flatMap_assoc]
  rw [hm] at e1
  let d := adv src dst OP SC σ (marks (marks (records.flatMap frame)))
    (records.flatMap frame).length
  have hlen : (records.flatMap frame).length≤cap := by omega
  have e2 := wrewind_spec cap src SC (records.flatMap frame).length d
    (by simp [d,adv,hSC]) (by simpa [d,adv,hSC] using hlen)
  let e := (d.setv SC 0).seth src (d.sh src-(records.flatMap frame).length)
  have eh : e=appendO σ dst OP (marks (marks (records.flatMap frame))) := by
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
  have e3 := emitWordM_spec cap dst OP [true,false,false] e
    (by rw [eh];simp [appendO,hd])
    (by rw [eh];simp only [appendO_val,Function.update_self,Codec.marks_length]
        norm_num only [List.length_cons,List.length_nil]
        omega)
  refine (e1.seq (e2.seq e3)).cast cap ?_ (by unfold appendRecordFieldCost;norm_num;omega)
  rw [eh,appendO_append]
  congr 1
  simp only [Codec.frame_eq_marks,Streaming.marks_append,marks,List.flatMap_append,
    List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]

end NearQuarticWires.StageTuple
