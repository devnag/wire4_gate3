import Proof.Quartic.StageGreedyCollector.BatchFramer

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyCollector

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.CounterAsm NearCubicGates.Close.Recovery.HTParts
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Expand.PolyTab

/-- `lem:print`, paper/paper.tex: tagged
framed replies retain every empty body with two physical delimiter bits. -/
theorem replyWord_length (replies : List (List Bool)) :
    (replyWord replies).length=2*replies.flatten.length+2*replies.length := by
  induction replies with
  | nil=>simp [replyWord]
  | cons bits replies ih=>
      simp only [replyWord,List.flatMap_cons,List.length_append,List.length_cons,frame_length] at ih ⊢
      simp only [List.flatten_cons,List.length_append]
      omega

/-- `lem:print`, paper/paper.tex: the
real batch reply contains the five common native fields, its binary
count, and all individually framed weak-cut bodies in original order. -/
structure ReplyRequest where
  fields : Fin 5→ℕ
  count : ℕ
  replies : List (List Bool)

def ReplyRequest.header (r : ReplyRequest) : List Bool :=(List.ofFn r.fields).flatMap natWord

def ReplyRequest.word (r : ReplyRequest) : List Bool :=r.header++natWord r.count++replyWord r.replies

def ReplyRequest.output (r : ReplyRequest) : List Bool :=frame (r.header++r.replies.flatten)

def ReplyRequest.capacity (r : ReplyRequest) : ℕ :=2*r.word.length+10

def ReplyRequest.steps (r : ReplyRequest) : ℕ :=300*(r.word.length+1)

/-- `lem:print`, paper/paper.tex: copy
the five actual common fields, skip the binary count by copying its bits
to scratch, then concatenate every real weak-cut reply in one output frame. -/
def finishReplies : WM 3 4 :=
  .seq (StagePacket.copyNaturalFields 1 1 3 (fun bit=>emitPair 2 0 bit) 5)
    (.seq (StagePacket.copyNaturalFields 1 1 3 (fun bit=>emitC 3 2 bit) 1)
      (.seq (.whs 1 (flattenReply 1 2 0)) (emitC 2 0 false)))

/-- `lem:print` and `prop:time`, paper/paper.tex: final concatenation is a linear pass over the actual
reply source; no global equality split or decoded cut count is introduced. -/
theorem finishReplies_spec (r : ReplyRequest) (a : WState 3 4)
    (hs : a.st 1=r.word) (hh : a.sh 1=0)
    (hout : a.st 2=[]) (hoh : a.sh 2=0) (hsc : a.st 3=[]) (hsch : a.sh 3=0)
    (hv : a.val=fun _=>0) :
    ∃ b,WExec r.capacity finishReplies a b (200*(r.word.length+1)) ∧ b.st 2=r.output := by
  have hflat : r.replies.flatten.length=(r.replies.map List.length).sum:=List.length_flatten
  have hl : r.word.length=r.header.length+(natWord r.count).length+
      2*r.replies.flatten.length+2*r.replies.length := by
    simp only [ReplyRequest.word,List.length_append,replyWord_length]
    omega
  have e1:=StagePacket.copyNaturalFields_spec r.capacity (1 : Fin 4) 2 (0 : Fin 4) 1 3
    (by decide) (by decide) (by decide) (by decide)
    (fun bit=>emitPair 2 0 bit) (fun bit=>[true,bit]) 15 2 (emits_pair (cap:=r.capacity))
    (by intro bit;rfl) (List.ofFn r.fields) [] (natWord r.count++replyWord r.replies) a
    (by simpa only [List.nil_append,ReplyRequest.word,ReplyRequest.header,List.append_assoc] using hs)
    hh (by rw [hout,hoh];rfl) (by rw [hv])
    (by rw [hv];change 0+2*r.header.length≤r.capacity;unfold ReplyRequest.capacity;omega)
    (by rw [hv];change 0+r.header.length≤r.capacity;unfold ReplyRequest.capacity;omega)
  simp only [List.length_ofFn] at e1
  let b:=adv (1 : Fin 4) 2 (0 : Fin 4) 1 a (Streaming.marks r.header) r.header.length
  have hb : b.st 1=r.header++[r.count].flatMap natWord++replyWord r.replies := by
    simp [b,adv,appendO,hs,ReplyRequest.word]
  have e2:=StagePacket.copyNaturalFields_spec r.capacity (1 : Fin 4) 3 (2 : Fin 4) 1 3
    (by decide) (by decide) (by decide) (by decide)
    (fun bit=>emitC 3 2 bit) (fun bit=>[bit]) 7 1 (emits_raw (cap:=r.capacity))
    (by intro bit;rfl) [r.count] r.header (replyWord r.replies) b hb
    (by rw [adv_sh_src,hh];omega)
    (by simp [b,adv,appendO,hsc,hsch]) (by simp [b,adv,appendO,hv])
    (by simp [b,adv,appendO,hv];unfold ReplyRequest.capacity
        have hn:=NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length r.count
        omega)
    (by rw [adv_val_SC,hv];simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,Nat.zero_add]
        unfold ReplyRequest.capacity;omega)
  have eid (bits : List Bool) : bits.flatMap (fun bit=>[bit])=bits:=by simp
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.length_singleton,eid] at e2
  let c:=adv (1 : Fin 4) 3 (2 : Fin 4) 1 b (natWord r.count) (natWord r.count).length
  have hc : c.st 1=(r.header++natWord r.count)++replyWord r.replies := by
    simp [c,b,adv,appendO,hs,ReplyRequest.word]
  have eh:=flattenReplies_spec r.capacity (1 : Fin 4) 2 (0 : Fin 4) (by decide)
    r.replies (r.header++natWord r.count) c hc
    (by simp [c,b,adv,appendO,hh,List.length_append])
    (by simp [c,b,adv,appendO,hout,hoh])
    (by simp [c,b,adv,appendO,hv];unfold ReplyRequest.capacity;omega)
  let d:=(appendO c 2 0 (Streaming.marks r.replies.flatten)).seth 1
    ((r.header++natWord r.count).length+(replyWord r.replies).length)
  have hd : d.sh 2=(d.st 2).length := by simp [d,c,b,adv,appendO,hout,hoh]
  have hdv : d.val 0<r.capacity := by
    simp [d,c,b,adv,appendO,hv]
    unfold ReplyRequest.capacity
    omega
  have ee:=emitC_spec r.capacity (2 : Fin 4) (0 : Fin 4) false d hd hdv
  refine ⟨_,(e1.seq (e2.seq (eh.seq ee))).mono ?_,?_⟩
  · change (r.header.length*28+5)+1+((natWord r.count).length*20+1+1+
      (30*(r.replies.flatten.length+r.replies.length)+1+1+7))≤_
    omega
  · change (appendO d 2 0 [false]).st 2=r.output
    simp [d,c,b,adv,appendO,hout,ReplyRequest.output,
      NearCubicGates.Close.Codec.frame_eq_marks,Streaming.marks_append]

/-- `lem:print`, paper/paper.tex: the
cold final pass loads its real framed batch reply once before the
header/count/body scan. -/
def finishProgram : WMX 3 4 :=
  .seq (.wm (StageGamma.unframeRecord 0 1 0)) (.wm finishReplies)

theorem finishProgram_run (r : ReplyRequest) :
    ∃ b,WXExec r.capacity finishProgram (idealStart 3 4 r.word (fun _=>0)) b r.steps ∧ b.st 2=r.output := by
  let a:=idealStart 3 4 r.word (fun _=>0)
  let b:=(a.sets 1 r.word).seth 0 (2*r.word.length+1)
  have e1 : WExec r.capacity (StageGamma.unframeRecord 0 1 0) a b (23*r.word.length+5) := by
    simpa [a,b,idealStart] using
      StageGamma.unframeRecord_run r.capacity (0 : Fin 4) 1 (by decide) (0 : Fin 4)
        r.word [] [] a (by simp [a,idealStart]) rfl rfl rfl
        (by unfold ReplyRequest.capacity;omega)
  obtain ⟨c,ec,hout⟩:=finishReplies_spec r b rfl rfl rfl rfl rfl rfl rfl
  exact ⟨c,(WXExec.seq (WXExec.wm e1) (WXExec.wm ec)).mono
    (by unfold ReplyRequest.steps;omega),hout⟩

/-- `lem:print` and `prop:time`, paper/paper.tex: one actual ordinary machine produces the common
native header followed by all reduced weak rows, with a linear full clock. -/
noncomputable def finishWordFunction :
    WordFunction ReplyRequest ReplyRequest.word ReplyRequest.output (fun r=>2*r.steps+2) :=
  wordFunction_of_ideal finishProgram 2 (by decide) ReplyRequest.capacity (fun _ _=>0)
    ReplyRequest.steps (fun _=>le_rfl) (by intro r;exact ⟨rfl,finishProgram_run r⟩)

end NearQuarticWires.StageGreedyCollector
