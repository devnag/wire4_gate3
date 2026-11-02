import Proof.Quartic.StageGreedyCollector.TagLoop
import Proof.Quartic.StageGreedyCollector.FrameAfter

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyCollector

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.CounterAsm NearCubicGates.Close.Recovery.HTParts

/-- `lem:print`, paper/paper.tex: retain
one finite context and copy the common header and binary request count;
only the unchanged raw entries remain under the source head. -/
def stagePrefix : WM 3 3 :=
  .seq (frameCopy 1 1 (fun bit=>emitC 3 0 bit))
    (.seq (frameCopy 1 1 (fun bit=>emitC 2 2 bit))
      (.seq (WM.rewind 2 2)
        (.seq (StagePacket.copyNaturalFields 1 1 2 (fun bit=>emitC 3 0 bit) 1)
          (.seq (.clear 1) (.clear 0)))))

def stagePrefixState (a : WState 3 3) (header context : List Bool) (count : ℕ) : WState 3 3 :=
  (((a.sets 2 (frame context)).sets 3 (frame header++natWord count)).seth 1
    ((frame header).length+(frame context).length+(natWord count).length)).seth 3
      ((frame header).length+(natWord count).length)

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual prefix is copied once, the finite context
is rewound, and all scratch counters are cleared before the streaming loop. -/
theorem stagePrefix_spec (cap : ℕ) (header context rest : List Bool) (count : ℕ)
    (a : WState 3 3)
    (hs : a.st 1=frame header++frame context++natWord count++rest)
    (hh : a.sh 1=0) (hcache : a.st 2=[]) (hch : a.sh 2=0)
    (hout : a.st 3=[]) (hoh : a.sh 3=0) (hv : a.val=fun _=>0)
    (hc : (frame header).length+(frame context).length+(natWord count).length≤cap) :
    WExec cap stagePrefix a (stagePrefixState a header context count)
      (100*((frame header).length+(frame context).length+(natWord count).length+1)) := by
  have eid (bits : List Bool) : bits.flatMap (fun bit=>[bit])=bits :=by simp
  have hc' :=hc
  simp only [frame_length,NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length] at hc'
  have e1:=frameCopy_spec cap (src:=1) (dst:=3) (OP:=0) (SC:=1)
    (by decide) (by decide) (emits_raw (cap:=cap)) (d:=1) (by intro bit;rfl)
    header [] (frame context++natWord count++rest) a
    (by simpa only [List.nil_append,List.append_assoc] using hs) hh
    (by rw [hout,hoh];rfl) (by rw [hv];simp only [Nat.zero_add,one_mul];omega)
    (by rw [hv];simp only [Nat.zero_add];omega)
  simp only [eid] at e1
  let b:=adv (1 : Fin 4) 3 (0 : Fin 3) 1 a (frame header) (frame header).length
  have hs1 : b.st 1=frame header++frame context++(natWord count++rest) := by
    simpa only [b,adv_st_src (by decide : (1 : Fin 4)≠3),List.append_assoc] using hs
  have e2:=frameCopy_spec cap (src:=1) (dst:=2) (OP:=2) (SC:=1)
    (by decide) (by decide) (emits_raw (cap:=cap)) (d:=1) (by intro bit;rfl)
    context (frame header) (natWord count++rest) b hs1
    (by rw [adv_sh_src,hh];omega)
    (by simp [b,adv,appendO,hcache,hch])
    (by simp [b,adv,appendO,hv];omega)
    (by rw [adv_val_SC,hv];simp only [Nat.zero_add];omega)
  simp only [eid] at e2
  let c:=adv (1 : Fin 4) 2 (2 : Fin 3) 1 b (frame context) (frame context).length
  have e3:=wrewind_spec cap (2 : Fin 4) (2 : Fin 3) (frame context).length c
    (by simp [c,b,adv,appendO,hv]) (by simp [c,b,adv,appendO,hv];omega)
  let d:=(c.seth 2 (c.sh 2-(frame context).length)).setv 2 0
  have hs2 : d.st 1=(frame header++frame context)++[count].flatMap natWord++rest := by
    simp [d,c,b,adv,appendO,hs,List.append_assoc]
  have e4:=StagePacket.copyNaturalFields_spec cap (1 : Fin 4) 3 (0 : Fin 3) 1 2
    (by decide) (by decide) (by decide) (by decide)
    (fun bit=>emitC 3 0 bit) (fun bit=>[bit]) 7 1 (emits_raw (cap:=cap)) (by intro bit;rfl)
    [count] (frame header++frame context) rest d hs2
    (by simp [d,c,b,adv,appendO,hh,List.length_append])
    (by simp [d,c,b,adv,appendO,hout,hoh]) rfl
    (by simp [d,c,b,adv,appendO,hv];omega)
    (by simp [d,c,b,adv,appendO,hv];omega)
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.length_singleton] at e4
  simp only [eid] at e4
  let e:=adv (1 : Fin 4) 3 (0 : Fin 3) 1 d (natWord count) (natWord count).length
  have e5:=wclear_spec cap (1 : Fin 3) (e.val 1) e rfl (by simp [e,d,c,b,adv,appendO,hv];omega)
  have e6:=wclear_spec cap (0 : Fin 3) ((e.setv 1 0).val 0) (e.setv 1 0) rfl
    (by simp [e,d,c,b,adv,appendO,hv];omega)
  refine (e1.seq (e2.seq (e3.seq (e4.seq (e5.seq e6))))).cast cap ?_ ?_
  · apply WState.eq
    · funext i;fin_cases i <;> simp [stagePrefixState,e,d,c,b,adv,appendO,hcache,hch,hout,hoh,hh]
    · funext i;fin_cases i <;> simp [stagePrefixState,e,d,c,b,adv,appendO,hcache,hout]
    · funext i;fin_cases i <;> simp [stagePrefixState,e,d,c,b,adv,appendO,hv]
    · rfl
  · simp [e,d,c,b,adv,appendO,hv]
    omega

end NearQuarticWires.StageGreedyCollector
