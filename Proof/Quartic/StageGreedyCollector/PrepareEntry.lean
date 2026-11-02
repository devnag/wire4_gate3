import Proof.Quartic.StageGreedyCollector.CopyContext
import Proof.Quartic.StageGreedyCollector.CopyEntry
import Proof.Quartic.StagePacket.Isolation

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyCollector

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks marks_length)
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CounterAsm
open NearCubicGates.Close.Recovery.HTParts
open NearQuarticWires.Reconstruct.Batch (appendT)

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: one physical
request contains a copied finite common context and precisely one
unchanged entry, with a final frame delimiter and reset local counters. -/
def prepareEntry (src cache dst : Fin (ns+1)) (OP SC K : Fin nr) : WM ns nr :=
  .seq (copyContext cache dst K)
    (.seq (copyEntryBody src dst OP SC K)
      (.seq (emitC dst OP false) (.seq (WM.clear SC) (WM.clear OP))))

/-- `lem:print` and `prop:time`, paper/paper.tex: one entry step reads no following entry, returns the
common-cache head, preserves every register and pays all actual bytes. -/
theorem prepareEntry_spec (cap : ℕ) (src cache dst : Fin (ns+1)) (OP SC K : Fin nr)
    (hsd : src≠dst) (hcd : cache≠dst)
    (hOS : OP≠SC) (hKO : K≠OP) (hKS : K≠SC)
    (context : List Bool) (entry : Entry) (pre suffix : List Bool) (a : WState ns nr)
    (hin : a.st src=pre++entry.word++suffix) (hh : a.sh src=pre.length)
    (hcache : a.st cache=frame context) (hch : a.sh cache=0)
    (hout : a.sh dst=(a.st dst).length)
    (hOP : a.val OP=0) (hSC : a.val SC=0) (hK : a.val K=0)
    (hc : 2*(context.length+entry.word.length)+2≤cap) :
    WExec cap (prepareEntry src cache dst OP SC K) a
      ((appendT a dst (frame (context++entry.word))).seth src (pre.length+entry.word.length))
      (100*(context.length+entry.word.length+1)) := by
  have ec:=copyContext_spec cap cache dst K hcd context [] a
    (by simpa only [List.append_nil] using hcache) hch hout hK (by omega)
  let b:=appendT a dst (marks context)
  have hbsource : b.st src=pre++entry.word++suffix := by
    simp [b,appendT,Function.update_of_ne hsd,hin]
  have hbhead : b.sh src=pre.length := by simp [b,appendT,Function.update_of_ne hsd,hh]
  have hbout : b.sh dst=(b.st dst).length := by simp [b,appendT,hout,List.length_append]
  have eb:=copyEntryBody_spec cap src dst OP SC K hsd hOS hKO hKS entry pre suffix b
    hbsource hbhead hbout hK (by change a.val OP+2*entry.word.length≤cap;rw [hOP];omega)
    (by change a.val SC+entry.word.length≤cap;rw [hSC];omega)
  let c:=adv src dst OP SC b (entry.word.flatMap fun bit=>[true,bit]) entry.word.length
  have hcSC : c.val SC=entry.word.length := by rw [adv_val_SC];change a.val SC+_= _;omega
  have hcOP : c.val OP=2*entry.word.length := by
    rw [adv_val_OP hOS,StagePacket.paired_length]
    change a.val OP+_= _
    omega
  have hcout : c.sh dst=(c.st dst).length := by rw [adv_sh_dst hsd,adv_st_dst,hbout,List.length_append]
  have ee:=NearCubicGates.Close.Codec.emitBit_spec cap dst OP false c hcout (by rw [hcOP];omega)
  let d:=appendO c dst OP [false]
  have hdSC : d.val SC=entry.word.length := by simp only [d,appendO_val,Function.update_of_ne hOS.symm,hcSC]
  have hdOP : d.val OP=2*entry.word.length+1 := by simp only [d,appendO_val,Function.update_self,hcOP,List.length_singleton]
  have es:=wclear_spec cap SC entry.word.length d hdSC (by rw [hdSC];omega)
  let e:=d.setv SC 0
  have heOP : e.val OP=2*entry.word.length+1 := by simp only [e,WState.setv_val,Function.update_of_ne hOS,hdOP]
  have eo:=wclear_spec cap OP (2*entry.word.length+1) e heOP (by rw [heOP];omega)
  have heq : e.setv OP 0=
      ((appendT a dst (frame (context++entry.word))).seth src (pre.length+entry.word.length)) := by
    have hbits : marks context++(entry.word.flatMap fun bit=>[true,bit])++[false]=
        frame (context++entry.word) := by
      rw [←StagePacket.paired_frame (context++entry.word),List.flatMap_append]
      rfl
    apply WState.eq
    · funext i
      by_cases hi : i=src
      · subst i
        simp [e,d,c,b,adv,appendO,appendT,hsd,hh]
      · by_cases ho : i=dst
        · subst i
          simp only [e,d,c,b,WState.setv_sh,appendO_sh,Function.update_self,
            adv_sh_dst hsd,appendT,WState.seth_sh,Function.update_self,WState.sets_sh,
            Function.update_of_ne hsd.symm,StagePacket.paired_length,Streaming.marks_length,
            List.length_singleton,frame_length,List.length_append]
          omega
        · simp [e,d,c,b,adv,appendO,appendT,Function.update_of_ne hi,Function.update_of_ne ho]
    · funext i
      by_cases ho : i=dst
      · subst i
        simp only [e,d,c,b,WState.setv_st,appendO_st,Function.update_self,adv_st_dst,
          appendT,WState.seth_st,WState.sets_st,Function.update_self]
        simp only [List.append_assoc] at hbits ⊢
        rw [hbits]
      · simp [e,d,c,b,adv,appendO,appendT,Function.update_of_ne ho]
    · funext j
      by_cases jo : j=OP
      · subst j;simp [e,d,c,b,adv,appendO,appendT,hOP]
      · by_cases js : j=SC
        · subst j;simp [e,d,c,b,adv,appendO,appendT,hOS.symm,hSC]
        · simp [e,d,c,b,adv,appendO,appendT,Function.update_of_ne jo,Function.update_of_ne js]
    · rfl
  have hword : entry.word.length=(entry.header.flatMap RepairRepresentation.natWord).length+
      (frame entry.payload).length := by simp only [Entry.word,List.length_append]
  exact (ec.seq (eb.seq (ee.seq (es.seq eo)))).cast cap heq (by omega)

end NearQuarticWires.StageGreedyCollector
