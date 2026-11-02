import Proof.Quartic.StageGreedyCollector.StagePrefix

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyCollector

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.CounterAsm NearCubicGates.Close.Recovery.HTParts

/-- `lem:print`, paper/paper.tex: the
first actual entry is located after one retained context and its encoded
count, without a numerical count or walk-index decode. -/
def firstPrefix : WM 4 3 :=
  .seq (frameCopy 1 1 (fun bit=>emitC 2 0 bit))
    (.seq (WM.rewind 2 0)
      (.seq (StagePacket.copyNaturalFields 1 1 2 (fun bit=>emitC 4 0 bit) 1)
        (.seq (.clear 1) (.clear 0))))

def firstPrefixState (a : WState 4 3) (context : List Bool) (count : ℕ) : WState 4 3 :=
  (((a.sets 2 (frame context)).sets 4 (natWord count)).seth 1
    ((frame context).length+(natWord count).length)).seth 4 (natWord count).length

/-- `lem:print` and `prop:time`, paper/paper.tex: the first-entry prefix reader stores the actual
context once, copies only the binary count, and leaves every later byte unread. -/
theorem firstPrefix_spec (cap : ℕ) (context rest : List Bool) (count : ℕ) (a : WState 4 3)
    (hs : a.st 1=frame context++natWord count++rest) (hh : a.sh 1=0)
    (hcache : a.st 2=[]) (hch : a.sh 2=0) (hout : a.st 4=[]) (hoh : a.sh 4=0)
    (hv : a.val=fun _=>0) (hc : (frame context).length+(natWord count).length≤cap) :
    WExec cap firstPrefix a (firstPrefixState a context count)
      (100*((frame context).length+(natWord count).length+1)) := by
  have eid (bits : List Bool) : bits.flatMap (fun bit=>[bit])=bits:=by simp
  have hc':=hc
  simp only [frame_length,NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length] at hc'
  have e1:=frameCopy_spec cap (src:=1) (dst:=2) (OP:=0) (SC:=1)
    (by decide) (by decide) (emits_raw (cap:=cap)) (d:=1) (by intro bit;rfl)
    context [] (natWord count++rest) a
    (by simpa only [List.nil_append,List.append_assoc] using hs) hh
    (by rw [hcache,hch];rfl) (by rw [hv];simp only [Nat.zero_add,one_mul];omega)
    (by rw [hv];simp only [Nat.zero_add];omega)
  simp only [eid] at e1
  let b:=adv (1 : Fin 5) 2 (0 : Fin 3) 1 a (frame context) (frame context).length
  have e2:=wrewind_spec cap (2 : Fin 5) (0 : Fin 3) (frame context).length b
    (by simp [b,adv,appendO,hv]) (by simp [b,adv,appendO,hv];omega)
  let c:=(b.setv 0 0).seth 2 (b.sh 2-(frame context).length)
  have hs1 : c.st 1=frame context++[count].flatMap natWord++rest := by
    simp [c,b,adv,appendO,hs]
  have e3:=StagePacket.copyNaturalFields_spec cap (1 : Fin 5) 4 (0 : Fin 3) 1 2
    (by decide) (by decide) (by decide) (by decide)
    (fun bit=>emitC 4 0 bit) (fun bit=>[bit]) 7 1 (emits_raw (cap:=cap)) (by intro bit;rfl)
    [count] (frame context) rest c hs1
    (by simp [c,b,adv,appendO,hh]) (by simp [c,b,adv,appendO,hout,hoh])
    (by simp [c,b,adv,appendO,hv])
    (by simp [c,b,adv,appendO,hv];omega) (by simp [c,b,adv,appendO,hv];omega)
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.length_singleton,eid] at e3
  let d:=adv (1 : Fin 5) 4 (0 : Fin 3) 1 c (natWord count) (natWord count).length
  have e4:=wclear_spec cap (1 : Fin 3) (d.val 1) d rfl (by simp [d,c,b,adv,appendO,hv];omega)
  have e5:=wclear_spec cap (0 : Fin 3) ((d.setv 1 0).val 0) (d.setv 1 0) rfl
    (by simp [d,c,b,adv,appendO,hv];omega)
  refine (e1.seq (e2.seq (e3.seq (e4.seq e5)))).cast cap ?_ ?_
  · apply WState.eq
    · funext i;fin_cases i <;> simp [firstPrefixState,d,c,b,adv,appendO,hcache,hch,hout,hoh,hh]
    · funext i;fin_cases i <;> simp [firstPrefixState,d,c,b,adv,appendO,hcache,hout]
    · funext i;fin_cases i <;> simp [firstPrefixState,d,c,b,adv,appendO,hv]
    · rfl
  · simp [d,c,b,adv,appendO,hv]
    omega

end NearQuarticWires.StageGreedyCollector
