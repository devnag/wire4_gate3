import Proof.Quartic.StagePrintTuple.RecordField
import Proof.Quartic.StagePrintTuple.UnaryHeaders
import Proof.Quartic.StagePrintTuple.RecordOutputs

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.CopyNat
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.TabMachine

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: the exact
Cartesian input consists of two real record streams, four physically
computed dimensions and five empty fields. -/
theorem childTupleInput_frame (r : StagePrint.ChildTupleRequest) :
    frame r.word=
      marks (frame ((fieldRecords r.L r.children).flatMap frame++[false]))++
      marks (frame ((fieldRecords r.L r.tuples).flatMap frame++[false]))++
      unaryHeaderBytes [r.N,r.M,r.children.length,r.tuples.length]++
      marks (List.replicate 5 false)++[false] := by
  simp [StagePrint.ChildTupleRequest.word,recStream_fieldNums,fieldsRecs_eq_records,
    Top.loadRec,Codec.frame_eq_marks,Streaming.marks_append,unaryHeaderBytes,
    List.replicate_succ,marks,List.append_assoc]

/-- `lem:print`, paper/paper.tex: the fixed
Cartesian input formatter reads retained child and tuple records and
persistent dimension registers, with no supplied compiled-input word. -/
def cartesianInputProgram (P : Fin 3 ↪ Fin (ns+1)) (R : Fin 8 ↪ Fin nr) : WM ns nr :=
  .seq (appendRecordFieldReset (P 0) (P 2) (R 0) (R 1))
    (.seq (appendRecordFieldReset (P 1) (P 2) (R 0) (R 1))
      (.seq (unaryHeaderProgram [R 4,R 5,R 6,R 7] (R 2) (R 3) (P 2) (R 0))
        (.seq (emitWordM (P 2) (R 0) (List.replicate 5 false))
          (.seq (emitC (P 2) (R 0) false) (WM.rewind (P 2) (R 0))))))

/-- `prop:time`, paper/paper.tex: all actual
record copying, dimension serialization and input rewind costs are
linear in the physically written Cartesian request. -/
def cartesianInputCost (r : StagePrint.ChildTupleRequest) : ℕ :=
  3000*((fieldRecords r.L r.children).flatMap frame |>.length)+
  3000*((fieldRecords r.L r.tuples).flatMap frame |>.length)+
  3000*(r.N+r.M+r.children.length+r.tuples.length+10)

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual child-step cold input is physically built
from original child records and the current suffix tuples. Source
cursors and formatter scratch are restored, while computed dimensions
and every other controller register remain unchanged. -/
theorem cartesianInputProgram_spec (cap : ℕ) (P : Fin 3 ↪ Fin (ns+1)) (R : Fin 8 ↪ Fin nr)
    (r : StagePrint.ChildTupleRequest) (preK preT restK restT : List Bool)
    (hendK : restK.headD false=false) (hendT : restT.headD false=false)
    (σ : WState ns nr)
    (hk : σ.st (P 0)=preK++(fieldRecords r.L r.children).flatMap frame++restK)
    (ht : σ.st (P 1)=preT++(fieldRecords r.L r.tuples).flatMap frame++restT)
    (hkh : σ.sh (P 0)=preK.length) (hth : σ.sh (P 1)=preT.length)
    (hd : σ.st (P 2)=[]) (hdh : σ.sh (P 2)=0)
    (hz : ∀i:Fin 4,σ.val (R (Fin.castAdd 4 i))=0)
    (hv : [R 4,R 5,R 6,R 7].map σ.val=[r.N,r.M,r.children.length,r.tuples.length])
    (hcap : 400*((fieldRecords r.L r.children).flatMap frame |>.length)+
      400*((fieldRecords r.L r.tuples).flatMap frame |>.length)+
      400*(r.N+r.M+r.children.length+r.tuples.length+10)≤cap) :
    WExec cap (cartesianInputProgram P R) σ
      (σ.sets (P 2) (frame r.word)) (cartesianInputCost r) := by
  have hp {i j : Fin 3} : P i=P j ↔ i=j := P.injective.eq_iff
  have hr {i j : Fin 8} : R i=R j ↔ i=j := R.injective.eq_iff
  have h0 : σ.val (R 0)=0 := hz 0
  have h1 : σ.val (R 1)=0 := hz 1
  have h2 : σ.val (R 2)=0 := hz 2
  have h3 : σ.val (R 3)=0 := hz 3
  have ek := appendRecordFieldReset_spec cap (P 0) (P 2) (R 0) (R 1)
    (P.injective.ne (by decide)) (R.injective.ne (by decide))
    (fieldRecords r.L r.children) preK restK (fieldRecords_nonempty r.L r.width_pos _) hendK σ
    hk hkh (by rw [hdh,hd];rfl) h1 (by rw [h0];omega)
  let a := appendO σ (P 2) (R 0)
    (marks (frame ((fieldRecords r.L r.children).flatMap frame++[false])))
  have et := appendRecordFieldReset_spec cap (P 1) (P 2) (R 0) (R 1)
    (P.injective.ne (by decide)) (R.injective.ne (by decide))
    (fieldRecords r.L r.tuples) preT restT (fieldRecords_nonempty r.L r.width_pos _) hendT a
    (by simp [a,appendO,hp,ht]) (by simp [a,appendO,hp,hth])
    (by simp [a,appendO,hdh,hd]) (by simp [a,appendO,hr,h1]) (by
      simp only [a,appendO_val,Function.update_self,h0,Codec.marks_length,
        Codec.frame_eq_marks,List.length_append,List.length_singleton]
      omega)
  let b := appendO a (P 2) (R 0)
    (marks (frame ((fieldRecords r.L r.tuples).flatMap frame++[false])))
  have hbvals : [R 4,R 5,R 6,R 7].map b.val=[r.N,r.M,r.children.length,r.tuples.length] := by
    simpa [b,a,appendO,hr] using hv
  have en := unaryHeaderProgram_spec cap [R 4,R 5,R 6,R 7] (R 2) (R 3) (P 2) (R 0)
    (R.injective.ne (by decide)) (R.injective.ne (by decide)) (R.injective.ne (by decide))
    (by
      intro A hA
      have hm : A=R 4 ∨ A=R 5 ∨ A=R 6 ∨ A=R 7 := by simpa using hA
      rcases hm with hm|hm|hm|hm <;> subst A <;> simp [hr]) b
    (by simp [b,a,appendO,hr,h2]) (by simp [b,a,appendO,hr,h3])
    (by simp [b,a,appendO,hdh,hd,List.length_append,Nat.add_assoc]) (by
      have hm := congrArg (fun ls : List ℕ=>(ls.map (fun j=>j+1)).sum) hbvals
      simp only [List.map_map,Function.comp_def] at hm
      rw [hm]
      simp only [b,a,appendO_val,Function.update_self,h0,Codec.marks_length,
        Codec.frame_eq_marks,List.length_append,List.length_singleton,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil]
      omega)
  rw [hbvals] at en
  let c := appendO b (P 2) (R 0) (unaryHeaderBytes [r.N,r.M,r.children.length,r.tuples.length])
  have hcval : c.val (R 0)=
      4*((fieldRecords r.L r.children).flatMap frame).length+
      4*((fieldRecords r.L r.tuples).flatMap frame).length+
      4*(r.N+r.M+r.children.length+r.tuples.length)+20 := by
    simp only [c,b,a,appendO_val,Function.update_self,h0,unaryHeaderBytes,
      Codec.marks_length,frame_length,List.length_append,List.length_singleton,
      List.flatMap_cons,List.flatMap_nil,List.length_nil,List.length_replicate]
    omega
  have ee := emitWordM_spec cap (P 2) (R 0) (List.replicate 5 false) c
    (by simp [c,b,a,appendO,hdh,hd,List.length_append,Nat.add_assoc])
    (by rw [hcval];norm_num only [List.length_replicate];omega)
  let d := appendO c (P 2) (R 0) (marks (List.replicate 5 false))
  have ed := Codec.emitBit_spec cap (P 2) (R 0) false d
    (by simp [d,c,b,a,appendO,hdh,hd,List.length_append,Nat.add_assoc])
    (by simp only [d,appendO_val,Function.update_self,Codec.marks_length,List.length_replicate]
        rw [hcval];omega)
  let e := appendO d (P 2) (R 0) [false]
  have he : e=appendO σ (P 2) (R 0) (frame r.word) := by
    simp only [e,d,c,b,a,appendO_append,childTupleInput_frame,List.append_assoc]
  have hlen : (frame r.word).length=c.val (R 0)+11 := by
    rw [childTupleInput_frame]
    simp only [List.length_append,Codec.marks_length,frame_length,
      List.length_singleton,List.length_replicate,unaryHeaderBytes,List.flatMap_cons,
      List.flatMap_nil,List.length_nil]
    rw [hcval]
    omega
  have ecap : (frame r.word).length≤cap := by
    rw [hlen,hcval]
    omega
  have er := wrewind_spec cap (P 2) (R 0) (frame r.word).length e
    (by rw [he];simp [appendO,h0]) (by rw [he];simp only [appendO_val,Function.update_self,h0,Nat.zero_add];exact ecap)
  refine (ek.seq (et.seq (en.seq (ee.seq (ed.seq er))))).cast cap ?_ ?_
  · rw [he]
    apply WState.eq
    · funext i
      by_cases hi:i=P 2
      · subst i;simp [appendO,hdh]
      · simp [appendO,Function.update_of_ne hi]
    · simp [appendO,hd]
    · funext i
      by_cases hi:i=R 0
      · subst i;simp [appendO,h0]
      · simp [appendO,Function.update_of_ne hi]
    · rfl
  · unfold appendRecordFieldCost unaryHeaderCost cartesianInputCost
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    rw [hlen,hcval]
    norm_num only [List.length_replicate]
    omega

end NearQuarticWires.StageTuple
