import Proof.Quartic.StageGreedyCollector.CopyContext

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyCollector

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Codec

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: an explicit
reply marker retains empty walk bodies without changing their order. -/
def replyWord (replies : List (List Bool)) : List Bool :=
  replies.flatMap fun bits=>true::frame bits

/-- `lem:print`, paper/paper.tex: one reply's
physical marker and frame are removed while its original body is
copied into the single final output frame. -/
def flattenReply (src dst : Fin (ns+1)) (OP : Fin nr) : WM ns nr :=
  .seq (.fwd src) (.seq (.whs src (copyPairW src dst OP)) (.fwd src))

theorem flattenReply_spec (cap : ℕ) (src dst : Fin (ns+1)) (OP : Fin nr)
    (hsd : src≠dst) (bits pre rest : List Bool) (a : WState ns nr)
    (hs : a.st src=pre++(true::frame bits)++rest) (hh : a.sh src=pre.length)
    (hd : a.sh dst=(a.st dst).length) (hc : a.val OP+2*bits.length≤cap) :
    WExec cap (flattenReply src dst OP) a
      ((appendO a dst OP (Streaming.marks bits)).seth src
        (pre.length+(true::frame bits).length)) (22*bits.length+5) := by
  have e1:=WExec.fwd (cap:=cap) src a
  let b:=a.seth src (a.sh src+1)
  have hb : b.st src=(pre++[true])++frame bits++rest := by
    simpa only [b,WState.seth_st,List.append_assoc,List.singleton_append] using hs
  have e2:=copyFrame_loop cap src dst hsd OP rest bits (pre++[true]) b hb
    (by simp [b,hh]) (by simpa [b,Function.update_of_ne hsd.symm] using hd)
    (by simpa [b] using hc)
  let c:=(appendO b dst OP (Streaming.marks bits)).seth src ((pre++[true]).length+2*bits.length)
  have e3:=WExec.fwd (cap:=cap) src c
  refine (e1.seq (e2.seq e3)).cast cap ?_ (by omega)
  apply WState.eq
  · funext i
    by_cases hi : i=src
    · subst i;simp [c,b,appendO,frame_length,List.length_append]
      omega
    · by_cases ho : i=dst
      · subst i;simp [c,b,appendO,Function.update_of_ne hsd.symm]
      · simp [c,b,appendO,Function.update_of_ne hi,Function.update_of_ne ho]
  · rfl
  · rfl
  · rfl

/-- `lem:print` and `prop:time`, paper/paper.tex: reply flattening is linear in the actual output bytes
and number of walks, including every empty or zero-weight reply. -/
theorem flattenReplies_spec (cap : ℕ) (src dst : Fin (ns+1)) (OP : Fin nr)
    (hsd : src≠dst) :
    ∀ (replies : List (List Bool)) (pre : List Bool) (a : WState ns nr),
      a.st src=pre++replyWord replies→a.sh src=pre.length→
      a.sh dst=(a.st dst).length→a.val OP+2*replies.flatten.length≤cap→
      WExec cap (.whs src (flattenReply src dst OP)) a
        ((appendO a dst OP (Streaming.marks replies.flatten)).seth src
          (pre.length+(replyWord replies).length))
        (30*(replies.flatten.length+replies.length)+1)
  | [],pre,a,hs,hh,_hd,_hc=>by
      have hbit : wbit a src=false := by
        simp only [replyWord,List.flatMap_nil,List.append_nil] at hs
        simp [wbit,readTapeBit,hs,hh]
      have he : ((appendO a dst OP (Streaming.marks ([].flatten : List Bool))).seth src
          (pre.length+(replyWord []).length))=a := by
        simp only [List.flatten_nil,Streaming.marks,List.flatMap_nil,NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO_nil,
          replyWord,List.length_nil,Nat.add_zero]
        rw [←hh,wseth_same]
      rw [he]
      simp only [List.flatten_nil,List.length_nil,Nat.add_zero,Nat.mul_zero,Nat.zero_add]
      exact WExec.whsF hbit
  | bits::replies,pre,a,hs,hh,hd,hc=>by
      have hp : a.st src=pre++(true::frame bits)++replyWord replies := by
        simpa only [replyWord,List.flatMap_cons,List.append_assoc] using hs
      have hbit : wbit a src=true := by simp [wbit,readTapeBit,hp,hh]
      have hcap : a.val OP+2*bits.length≤cap := by
        simp only [List.flatten_cons,List.length_append] at hc
        omega
      have e1:=flattenReply_spec cap src dst OP hsd bits pre (replyWord replies) a hp hh hd hcap
      let b:=(appendO a dst OP (Streaming.marks bits)).seth src (pre.length+(true::frame bits).length)
      have hbsource : b.st src=(pre++(true::frame bits))++replyWord replies := by
        simp [b,appendO,Function.update_of_ne hsd,hp,List.append_assoc]
      have hbhead : b.sh src=(pre++(true::frame bits)).length := by simp [b,List.length_append]
      have hbout : b.sh dst=(b.st dst).length := by
        simp [b,appendO,Function.update_of_ne hsd.symm,hd,List.length_append]
      have hbcap : b.val OP+2*replies.flatten.length≤cap := by
        simp only [b,WState.seth_val,appendO_val,Function.update_self,Streaming.marks_length]
        simp only [List.flatten_cons,List.length_append] at hc
        omega
      have e2:=flattenReplies_spec cap src dst OP hsd replies (pre++(true::frame bits)) b
        hbsource hbhead hbout hbcap
      refine (WExec.whsT hbit e1 e2).cast cap ?_ ?_
      · apply WState.eq
        · funext i
          by_cases hi : i=src
          · subst i;simp [b,appendO,replyWord,List.length_append]
            omega
          · by_cases ho : i=dst
            · subst i;simp [b,appendO,hsd.symm,Streaming.marks_length,List.length_append]
              omega
            · simp [b,appendO,Function.update_of_ne hi,Function.update_of_ne ho]
        · funext i
          by_cases ho : i=dst
          · subst i;simp [b,appendO,Streaming.marks_append,List.append_assoc]
          · simp [b,appendO,Function.update_of_ne ho]
        · funext j
          by_cases hj : j=OP
          · subst j;simp [b,appendO,Streaming.marks_length,List.length_append]
            omega
          · simp [b,appendO,Function.update_of_ne hj]
        · rfl
      · simp only [List.flatten_cons,List.length_append,List.length_cons]
        omega

end NearQuarticWires.StageGreedyCollector
