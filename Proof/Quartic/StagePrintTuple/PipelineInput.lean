import Proof.Quartic.StagePrintTuple.NestedField
import Proof.Quartic.StagePrint.OriginalPipeline

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.CopyNat
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close NearCubicGates.Close.WordPrograms

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: an actual
original-call source, original-child unary index and affine header
constitute the three nonempty fields of the existing row printer. -/
def pipelineInputWord (source index header : List Bool) : List Bool :=
  Top.loadRec (frame source) (frame index) (frame header) [] [] [] [] [] [] [] []

/-- `lem:print`, paper/paper.tex: the physical
nested input construction writes the exact existing eleven-field codec
and its ordinary outer frame, including all eight empty trailing fields. -/
theorem pipelineInputWord_frame (a b c : List Bool) :
    frame (pipelineInputWord a b c)=
      marks (frame (frame a))++marks (frame (frame b))++marks (frame (frame c))++
        marks (List.replicate 8 false)++[false] := by
  simp [pipelineInputWord,Top.loadRec,Codec.frame_eq_marks,
    Streaming.marks_append,marks,List.replicate_succ,List.append_assoc]

/-- `lem:print`, paper/paper.tex: three real
retained source tapes are nested into the existing cold row-printer
input, then every output and source cursor is physically reset. -/
def pipelineInputProgram (P : Fin 4 ↪ Fin (ns+1)) (OP SC : Fin nr) : WM ns nr :=
  .seq (appendNestedFieldReset (P 0) (P 3) OP SC)
    (.seq (appendNestedFieldReset (P 1) (P 3) OP SC)
      (.seq (appendNestedFieldReset (P 2) (P 3) OP SC)
        (.seq (emitWordM (P 3) OP (List.replicate 8 false))
          (.seq (emitC (P 3) OP false) (WM.rewind (P 3) OP)))))

/-- `prop:time`, paper/paper.tex: the original
row request is formatted in linear time in its three actual byte fields. -/
def pipelineInputCost (a b c : List Bool) : ℕ :=
  1500*((frame a).length+(frame b).length+(frame c).length+1)

/-- `lem:print` and `prop:time`, paper/paper.tex: the genuine original-source row request is physically
constructed on an initially empty call-input tape. Every marker, empty
field and source rewind is included, with no preinstalled row input. -/
theorem pipelineInputProgram_spec (cap : ℕ) (P : Fin 4 ↪ Fin (ns+1)) (OP SC : Fin nr)
    (hOS : OP≠SC) (a b c : List Bool) (σ : WState ns nr)
    (ha : σ.st (P 0)=frame a) (hb : σ.st (P 1)=frame b) (hc : σ.st (P 2)=frame c)
    (hh : ∀ i : Fin 4,σ.sh (P i)=0) (hd : σ.st (P 3)=[])
    (hOP : σ.val OP=0) (hSC : σ.val SC=0)
    (hcap : 4*((frame a).length+(frame b).length+(frame c).length)+100≤cap) :
    WExec cap (pipelineInputProgram P OP SC) σ
      (σ.sets (P 3) (frame (pipelineInputWord a b c))) (pipelineInputCost a b c) := by
  have hp {i j : Fin 4} : P i=P j ↔ i=j := P.injective.eq_iff
  have hcap' := hcap
  simp only [Codec.frame_eq_marks,List.length_append,List.length_singleton,Codec.marks_length] at hcap'
  have e1 := appendNestedFieldReset_spec cap (P 0) (P 3) OP SC
    (P.injective.ne (by decide)) hOS a [] σ (by simpa using ha) (hh 0)
    (by simp [hh,hd]) hSC (by rw [hOP];omega)
  let s1 := appendO σ (P 3) OP (marks (frame (frame a)))
  have e2 := appendNestedFieldReset_spec cap (P 1) (P 3) OP SC
    (P.injective.ne (by decide)) hOS b [] s1
    (by simp [s1,appendO,hp,hb]) (by simp [s1,appendO,hp,hh])
    (by simp [s1,appendO,hh,hd]) (by simp [s1,appendO,hOS.symm,hSC])
    (by simp only [s1,appendO_val,Function.update_self,hOP,Codec.marks_length,
      Codec.frame_eq_marks,List.length_append,List.length_singleton];omega)
  let s2 := appendO s1 (P 3) OP (marks (frame (frame b)))
  have e3 := appendNestedFieldReset_spec cap (P 2) (P 3) OP SC
    (P.injective.ne (by decide)) hOS c [] s2
    (by simp [s2,s1,appendO,hp,hc]) (by simp [s2,s1,appendO,hp,hh])
    (by simp [s2,s1,appendO,hh,hd,List.length_append,Nat.add_assoc])
    (by simp [s2,s1,appendO,hOS.symm,hSC])
    (by simp only [s2,s1,appendO_val,Function.update_self,hOP,Codec.marks_length,
      Codec.frame_eq_marks,List.length_append,List.length_singleton];omega)
  let s3 := appendO s2 (P 3) OP (marks (frame (frame c)))
  have e4 := emitWordM_spec cap (P 3) OP (List.replicate 8 false) s3
    (by simp [s3,s2,s1,appendO,hh,hd,List.length_append,Nat.add_assoc])
    (by simp [s3,s2,s1,appendO,hOP,Codec.marks_length,Codec.frame_eq_marks,
      List.length_append];omega)
  let s4 := appendO s3 (P 3) OP (marks (List.replicate 8 false))
  have e5 := Codec.emitBit_spec cap (P 3) OP false s4
    (by simp [s4,s3,s2,s1,appendO,hh,hd,List.length_append,Nat.add_assoc])
    (by simp [s4,s3,s2,s1,appendO,hOP,Codec.marks_length,Codec.frame_eq_marks,
      List.length_append];omega)
  let s5 := appendO s4 (P 3) OP [false]
  have hs5 : s5=appendO σ (P 3) OP (frame (pipelineInputWord a b c)) := by
    simp only [s5,s4,s3,s2,s1,appendO_append,pipelineInputWord_frame,List.append_assoc]
  have e6 := wrewind_spec cap (P 3) OP (frame (pipelineInputWord a b c)).length s5
    (by rw [hs5];simp [appendO,hOP])
    (by rw [hs5,pipelineInputWord_frame];simp [appendO,hOP,Codec.marks_length,
      Codec.frame_eq_marks,List.length_append];omega)
  refine (e1.seq (e2.seq (e3.seq (e4.seq (e5.seq e6))))).cast cap ?_ ?_
  · rw [hs5]
    apply WState.eq
    · funext i
      by_cases hi : i=P 3
      · subst hi;simp [appendO,hh]
      · simp [appendO,Function.update_of_ne hi]
    · simp [appendO,hd]
    · funext i
      by_cases hi : i=OP
      · subst hi;simp [appendO,hOP]
      · simp [appendO,Function.update_of_ne hi]
    · rfl
  · unfold pipelineInputCost appendNestedFieldCost
    rw [pipelineInputWord_frame]
    simp [Codec.marks_length,Codec.frame_eq_marks,List.length_append]
    omega

end NearQuarticWires.StageTuple
