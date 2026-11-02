import Proof.Quartic.StageTupleInputs.NativeLayout
import Proof.Wire_3_5.PrimAsmCopyNat

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTupleInputs

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.CopyNat
open NearCubicGates.Close
open StageTuple StageStackInput

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: a genuine native
child-pool cold input is constructed by reading five retained source
frames; no decoded request or extra input scalar is installed. -/
def nativeKidsInputProgram (P : Fin 6↪Fin (ns+1)) (R : Fin 2↪Fin nr) : WM ns nr :=
  .seq (appendNestedFieldReset (P 0) (P 5) (R 0) (R 1))
    (.seq (appendNestedFieldReset (P 1) (P 5) (R 0) (R 1))
      (.seq (cachedFramesProgram [P 2,P 3,P 4] (P 5) (R 0) (R 1))
        (.seq (emitWordM (P 5) (R 0) (List.replicate 6 false))
          (.seq (emitC (P 5) (R 0) false) (WM.rewind (P 5) (R 0))))))

/-- `lem:print` and `prop:time`, paper/paper.tex: exact packet bytes and complete state restoration meet
the checked consumer contract at its unchanged linear clock/capacity. -/
theorem nativeKidsInputProgram_spec :
    StageTuple.NativeKidsInputSpec (ns:=ns) (nr:=nr) nativeKidsInputProgram := by
  intro cap P R a b c d e σ ha hb hc hd he hout hheads hz hcap
  have hp {i j : Fin 6} : P i=P j↔i=j := P.injective.eq_iff
  have hr {i j : Fin 2} : R i=R j↔i=j := R.injective.eq_iff
  have h0 : σ.val (R 0)=0 := hz 0
  have h1 : σ.val (R 1)=0 := hz 1
  have hdh : σ.sh (P 5)=0 := hheads 5
  unfold nativeKidsInputMagnitude at hcap
  have ea:=appendNestedFieldReset_spec cap (P 0) (P 5) (R 0) (R 1)
    (P.injective.ne (by decide)) (R.injective.ne (by decide)) a [] σ
    (by simpa only [List.append_nil] using ha) (hheads 0) (by rw [hdh,hout];rfl) h1
    (by rw [h0];omega)
  let u:=appendO σ (P 5) (R 0) (marks (frame (frame a)))
  have uv : u.val (R 0)=4*(frame a).length+2 := by
    simp only [u,appendO_val,Function.update_self,h0,Codec.marks_length,frame_length]
    omega
  have eb:=appendNestedFieldReset_spec cap (P 1) (P 5) (R 0) (R 1)
    (P.injective.ne (by decide)) (R.injective.ne (by decide)) b [] u
    (by simp [u,appendO,hp,hb]) (by simp [u,appendO,hp,hheads 1])
    (by simp [u,appendO,hdh,hout]) (by simp [u,appendO,hr,h1]) (by rw [uv];omega)
  let v:=appendO u (P 5) (R 0) (marks (frame (frame b)))
  have vv : v.val (R 0)=4*(frame a).length+4*(frame b).length+4 := by
    simp only [v,appendO_val,Function.update_self,Codec.marks_length,frame_length]
    rw [uv]
    simp only [frame_length]
    omega
  let fields : List (Fin (ns+1)×List Bool):=[(P 2,c),(P 3,d),(P 4,e)]
  have hsrc : ∀q∈fields,q.1≠P 5 := by
    intro q hq
    simp only [fields,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl <;> exact P.injective.ne (by decide)
  have hdata : ∀q∈fields,v.st q.1=frame q.2 ∧ v.sh q.1=0 := by
    intro q hq
    simp only [fields,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl
    · simp [v,u,appendO,hp,hc,hheads 2]
    · simp [v,u,appendO,hp,hd,hheads 3]
    · simp [v,u,appendO,hp,he,hheads 4]
  have es:=cachedFramesProgram_spec cap (P 5) (R 0) (R 1) (R.injective.ne (by decide))
    fields hsrc v hdata (by simp [v,u,appendO,hdh,hout,List.length_append,Nat.add_assoc])
    (by simp [v,u,appendO,hr,h1]) (by
      change v.val (R 0)+(cachedFramesBytes [c,d,e]).length+1≤cap
      rw [vv,nativeCached_length]
      omega)
  change WExec cap (cachedFramesProgram [P 2,P 3,P 4] (P 5) (R 0) (R 1)) v
    (appendO v (P 5) (R 0) (cachedFramesBytes [c,d,e])) (cachedFramesCost [c,d,e]) at es
  let w:=appendO v (P 5) (R 0) (cachedFramesBytes [c,d,e])
  have wv : w.val (R 0)=4*(frame a).length+4*(frame b).length+
      2*(frame c).length+2*(frame d).length+2*(frame e).length+4 := by
    simp only [w,appendO_val,Function.update_self,nativeCached_length]
    rw [vv]
    omega
  have ee:=emitWordM_spec cap (P 5) (R 0) (List.replicate 6 false) w
    (by simp [w,v,u,appendO,hdh,hout,List.length_append,Nat.add_assoc])
    (by rw [wv];norm_num only [List.length_replicate];omega)
  let x:=appendO w (P 5) (R 0) (marks (List.replicate 6 false))
  have ed:=Codec.emitBit_spec cap (P 5) (R 0) false x
    (by simp [x,w,v,u,appendO,hdh,hout,List.length_append,Nat.add_assoc])
    (by simp only [x,appendO_val,Function.update_self,Codec.marks_length,List.length_replicate]
        rw [wv];omega)
  let y:=appendO x (P 5) (R 0) [false]
  have hy : y=appendO σ (P 5) (R 0) (frame (nativeKidsInputWord a b c d e)) := by
    simp only [y,x,w,v,u,appendO_append,nativeInput_frame,List.append_assoc]
  have hl : (frame (nativeKidsInputWord a b c d e)).length=w.val (R 0)+13 := by
    rw [nativeInput_length,wv]
  have hlen : (frame (nativeKidsInputWord a b c d e)).length≤cap := by
    rw [hl,wv]
    omega
  have er:=wrewind_spec cap (P 5) (R 0) (frame (nativeKidsInputWord a b c d e)).length y
    (by rw [hy];simp [appendO,h0])
    (by rw [hy];simp only [appendO_val,Function.update_self,h0,Nat.zero_add];exact hlen)
  refine (ea.seq (eb.seq (es.seq (ee.seq (ed.seq er))))).cast cap ?_ ?_
  · rw [hy]
    apply WState.eq
    · funext i
      by_cases hi:i=P 5
      · subst i;simp [appendO,hdh]
      · simp [appendO,Function.update_of_ne hi]
    · simp [appendO,hout]
    · funext i
      by_cases hi:i=R 0
      · subst i;simp [appendO,h0]
      · simp [appendO,Function.update_of_ne hi]
    · rfl
  · rw [nativeCached_cost,hl,wv]
    unfold appendNestedFieldCost nativeKidsInputMagnitude
    norm_num only [List.length_replicate]
    omega

end NearQuarticWires.StageTupleInputs
