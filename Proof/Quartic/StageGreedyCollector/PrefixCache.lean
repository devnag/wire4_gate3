import Proof.Quartic.StageGamma.Retain
import Proof.Quartic.StageGreedyCollector.FrameAfter

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyCollector

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Codec
open NearCubicGates.Close.CounterMachine NearCubicGates.Close.CounterAsm
open NearCubicGates.Close.Recovery.HTParts NearCubicGates.Close.Expand.PolyTab
open StageGamma

variable {Request : Type} {input cache : Request→List Bool} {budget : Request→ℕ}

/-- `lem:print`, paper/paper.tex: the
computed common header is placed before the retained original source,
with its own exact frame and one physical call. -/
noncomputable def prefixProgram
    (f : WordFunction Request input (fun r=>frame (cache r)) budget) :
    WMX (f.program.tapeCount+2) 3 :=
  let t:=f.program.tapeCount
  .seq (.wm (copyRW 0 (retainedMap t (tape0 f.program)) 0 1 2))
    (.seq (.machZ f.program.machine (retainedMap t) (retainedRuler t))
      (.seq (.wm (frameCopy (retainedMap t f.program.outputTape) 1
        (fun bit=>emitPair (retainedOut t) 0 bit)))
        (.seq (.wm (.whs 0 (copyPairW 0 (retainedOut t) 0)))
          (.wm (emitC (retainedOut t) 0 false)))))

def prefixCapacity (r : Request) : ℕ := 10*((input r).length+(cache r).length+1)+10

def prefixCost (r : Request) : ℕ := 2*budget r+300*((input r).length+(cache r).length+1)

/-- `lem:print` and `prop:time`, paper/paper.tex: the header is computed from one real source copy;
the original source and complete computed header are then physically
written in their required order, with every copied bit charged. -/
theorem prefix_run
    (f : WordFunction Request input (fun r=>frame (cache r)) budget) (r : Request) :
    ∃ b, WXExec (prefixCapacity (input:=input) (cache:=cache) r) (prefixProgram f)
      (idealStart (f.program.tapeCount+2) 3 (input r)
        (retainedLens f.program.tapeCount (budget r))) b
      (prefixCost (input:=input) (cache:=cache) (budget:=budget) r) ∧
      b.st (retainedOut f.program.tapeCount)=frame (frame (cache r)++input r) := by
  let t := f.program.tapeCount
  let cap := prefixCapacity (input := input) (cache := cache) r
  let σ := idealStart (t + 2) 3 (input r) (retainedLens t (budget r))
  have ht : 2 ≤ t := f.program.twoTapes
  have hm0 : retainedMap t (tape0 f.program) = (1 : Fin (t + 3)) := by
    apply Fin.ext
    change (0 + 1 : ℕ) = 1 % (t + 3)
    rw [Nat.mod_eq_of_lt (by omega)]
  have hsrc : σ.st 0 = frame (input r) := by simp [σ, idealStart]
  have hdst : σ.st (retainedMap t (tape0 f.program)) = [] := by
    simp [σ, idealStart, retainedLens, retainedMap, tape0]
    omega
  have hc := copyRW_spec cap (0 : Fin (t + 3)) (retainedMap t (tape0 f.program))
    ((retainedMap_off t (tape0 f.program)).1.symm) (0 : Fin 3) 1 2
    (by decide) (by decide) (by decide)
    (input r) [] σ (by simpa using hsrc) rfl hdst rfl rfl rfl rfl
    (by dsimp [cap, prefixCapacity]; omega)
  let σ1 := σ.sets (retainedMap t (tape0 f.program)) (frame (input r))
  have h1in : σ1.st (retainedMap t (tape0 f.program)) = frame (input r) := by simp [σ1]
  have h1blank : ∀ j, j ≠ tape0 f.program → σ1.st (retainedMap t j) = [] := by
    intro j hj
    have hne : retainedMap t j ≠ retainedMap t (tape0 f.program) :=
      fun h => hj (retainedMap_injective t h)
    have hjr := retainedMap_ne_ruler t j
    have hj0 := (retainedMap_off t j).1
    simp only [σ1, WState.sets_st, Function.update_of_ne hne]
    simp [σ, idealStart, retainedLens, retainedMap]
    omega
  have h1ruler : σ1.st (retainedRuler t) = List.replicate (budget r) false := by
    have hne := (retainedMap_ne_ruler t (tape0 f.program)).symm
    simp only [σ1, WState.sets_st, Function.update_of_ne hne]
    simp [σ, idealStart, retainedRuler, retainedLens]
  obtain ⟨σ2, hcall, houtput, hheads, hoff, hregs⟩ :=
    wfDock_exact f r cap (retainedMap t) (retainedMap_injective t) (retainedRuler t)
      (retainedMap_ne_ruler t) σ1 h1in h1blank (fun _ => rfl)
      (budget r) h1ruler rfl le_rfl
  have h20 := hoff 0 (fun j => (retainedMap_off t j).1)
  have h2out := hoff (retainedOut t) (fun j => (retainedMap_off t j).2)
  have hσ2src : σ2.st 0 = frame (input r) := by
    rw [h20.1]
    simp [σ1, (retainedMap_off t (tape0 f.program)).1.symm, hsrc]
  have hσ2out : σ2.st (retainedOut t) = [] := by
    rw [h2out.1]
    simp only [σ1, WState.sets_st,
      Function.update_of_ne (retainedMap_off t (tape0 f.program)).2.symm]
    simp [σ, idealStart, retainedOut, retainedLens]
  have hσ2h0 : σ2.sh 0 = 0 := h20.2
  have hσ2hout : σ2.sh (retainedOut t) = 0 := h2out.2
  have hv0 : σ2.val 0 = 0 := by rw [hregs]; rfl
  have hv1 : σ2.val 1=0 :=by rw [hregs];rfl
  have hfirst:=frameCopy_spec cap
    ((retainedMap_off t f.program.outputTape).2) (by decide : (0 : Fin 3)≠1)
    (emits_pair (cap:=cap)) (d:=2) (by intro bit;rfl) (cache r) [] [] σ2
    (by simpa only [List.nil_append,List.append_nil] using houtput) (hheads _)
    (by rw [hσ2hout,hσ2out];rfl)
    (by rw [hv0];simp only [frame_length];dsimp [cap,prefixCapacity];omega)
    (by rw [hv1];simp only [frame_length];dsimp [cap,prefixCapacity];omega)
  let σ3:=adv (retainedMap t f.program.outputTape) (retainedOut t) (0 : Fin 3) 1 σ2
    ((frame (cache r)).flatMap fun bit=>[true,bit]) (frame (cache r)).length
  have hs3 : σ3.st 0=frame (input r) := by
    simp [σ3,adv,appendO,show (0 : Fin (t+3))≠retainedOut t by simp [retainedOut],hσ2src]
  have hh3 : σ3.sh 0=0 := by
    simp [σ3,adv,appendO,(retainedMap_off t f.program.outputTape).1.symm,
      show (0 : Fin (t+3))≠retainedOut t by simp [retainedOut],hσ2h0]
  have hd3 : σ3.sh (retainedOut t)=(σ3.st (retainedOut t)).length := by
    rw [adv_sh_dst (retainedMap_off t f.program.outputTape).2,adv_st_dst,hσ2hout,hσ2out]
    simp
  have hv3 : σ3.val 0=2*(frame (cache r)).length := by
    rw [adv_val_OP (by decide),StagePacket.paired_length,hv0];omega
  have hsecond:=copyFrame_loop cap (0 : Fin (t+3)) (retainedOut t)
    (by simp [retainedOut]) (0 : Fin 3) [] (input r) [] σ3
    (by simpa only [List.nil_append,List.append_nil] using hs3) hh3 hd3
    (by rw [hv3];simp only [frame_length];dsimp [cap,prefixCapacity];omega)
  simp only [List.length_nil,Nat.zero_add] at hsecond
  let σ4:=(appendO σ3 (retainedOut t) 0 (Streaming.marks (input r))).seth 0 (2*(input r).length)
  have hout4 : σ4.st (retainedOut t)=
      ((frame (cache r)).flatMap fun bit=>[true,bit])++Streaming.marks (input r) := by
    simp [σ4,σ3,adv,appendO,hσ2out]
  have hh4 : σ4.sh (retainedOut t)=(σ4.st (retainedOut t)).length := by
    simp only [σ4,WState.seth_sh,WState.seth_st,
      Function.update_of_ne (show retainedOut t≠(0 : Fin (t+3)) by simp [retainedOut]),
      appendO_sh,Function.update_self,appendO_st,hd3,List.length_append]
  have hc4 : σ4.val 0<cap := by
    simp only [σ4,WState.seth_val,appendO_val,Function.update_self,hv3,Streaming.marks_length,frame_length]
    dsimp [cap,prefixCapacity];omega
  have hlast:=emitC_spec cap (retainedOut t) (0 : Fin 3) false σ4 hh4 hc4
  refine ⟨_,(WXExec.seq (WXExec.wm hc) (WXExec.seq hcall
    (WXExec.seq (WXExec.wm hfirst) (WXExec.seq (WXExec.wm hsecond) (WXExec.wm hlast))))).mono ?_,?_⟩
  · dsimp [prefixCost]
    simp only [frame_length]
    omega
  · change (appendO σ4 (retainedOut t) 0 [false]).st (retainedOut t)=_
    simp only [appendO_st,Function.update_self,hout4]
    rw [NearCubicGates.Close.Codec.frame_eq_marks (frame (cache r)++input r),Streaming.marks_append]
    rfl

/-- `lem:print` and `prop:time`, paper/paper.tex: one fixed ordinary machine places the genuinely
computed header before its original source, retaining the same paid call. -/
noncomputable def prefixWordFunction
    (f : WordFunction Request input (fun r=>frame (cache r)) budget) :
    WordFunction Request input (fun r=>frame (frame (cache r)++input r))
      (fun r=>2*prefixCost (input:=input) (cache:=cache) (budget:=budget) r+2) :=
  wordFunction_of_ideal (prefixProgram f) (retainedOut f.program.tapeCount)
    (by simp [retainedOut]) (prefixCapacity (input:=input) (cache:=cache))
    (fun r=>retainedLens f.program.tapeCount (budget r))
    (prefixCost (input:=input) (cache:=cache) (budget:=budget)) (fun _=>le_rfl) (by
      intro r
      refine ⟨?_,prefix_run f r⟩
      simp [retainedLens,retainedOut])

end NearQuarticWires.StageGreedyCollector
