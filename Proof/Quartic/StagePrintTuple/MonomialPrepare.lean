import Proof.Quartic.StagePrintTuple.CachedCall
import Proof.Quartic.StagePrintTuple.RememberFrame
import Proof.Quartic.StagePrintTuple.KernelMaps
import Proof.Quartic.StagePrintTuple.CallPreserve
import Proof.Quartic.StagePrintTuple.KernelInitialize
import Proof.Gates.Codec.PairFrame

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.FinalPass.Hash4
open NearCubicGates.Close.Interfaces NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.TabMachine
open NearCubicGates.Close.WordPrograms.SInt (encS)
open NearQuarticWires.Control

/-- `lem:print`, paper/paper.tex: the actual
prepared monomial measures its support cache, decodes its real support
count, initializes the reverse/tuple counters and obtains its signed
coefficient field from the genuine isolated coefficient machine. -/
noncomputable def monomialPrepareProgram (span : ℕ)
    (hp : coefficientWordFunction.program.tapeCount ≤ span) : WMX (span+29) 32 :=
  .seq (.wm (rememberFrameProgram (kernelLocal span 14) 1 26 6))
    (.seq (.wm (readNatM true (kernelLocal span 14) 0 1 16 2 3))
      (.seq (.wm (wcopyR 16 15 6))
        (.seq (.wm (.inc 14))
          (cachedCallProgram (kernelSite span coefficientWordFunction.program hp)
            (kernelLocal span 15) (kernelLocal span 16) 0 1 2))))

/-- `lem:print`, paper/paper.tex: the exact
reverse-ready state contains the measured support length, actual
support/reverse counters, singleton empty tuple and real coefficient reply. -/
def monomialPrepareState (span L : ℕ) (support : List ℕ) (coefficient : ℤ)
    (σ : WState (span+29) 32) : WState (span+29) 32 :=
  let a := σ.setv 26 (frame (listWord natWord support)).length
  let b := (a.seth (kernelLocal span 14) (marks (natWord support.length)).length).setv 16 support.length
  (((b.setv 15 support.length).setv 14 1).sets (kernelLocal span 16)
    (CoefficientRequest.output ⟨L,coefficient⟩))

/-- `prop:time`, paper/paper.tex: preparation
uses only actual support/coefficient packets, real support count and
the genuine small coefficient-call budget in its analysis capacity. -/
def monomialPrepareCapacity (L : ℕ) (support : List ℕ) (coefficient : ℤ) : ℕ :=
  let q : CoefficientRequest := ⟨L,coefficient⟩
  ([(frame (listWord natWord support)).length,2^(natBitLength support.length+1),support.length,1,
    4*q.word.length+4,2*q.word.length+2+q.budget,q.output.length+1] : List ℕ).sum

/-- `prop:time`, paper/paper.tex: each actual
support-measure/count operation and isolated coefficient call is paid
additively, with all four source sequence transitions included. -/
def monomialPrepareCost (L : ℕ) (support : List ℕ) (coefficient : ℤ) : ℕ :=
  let q : CoefficientRequest := ⟨L,coefficient⟩
  60*((frame (listWord natWord support)).length+1)+1+
    (scalarReadCost support.length+1+((18*support.length+3)+1+
      (3+1+cachedCallCost q.word.length q.budget q.output.length)))

/-- `lem:print` and `prop:time`, paper/paper.tex: genuine small source packets establish the complete
reverse-ready monomial state. Every count, byte counter and coefficient
field is physically computed, with no decoded-value input premise. -/
theorem monomialPrepareProgram_spec (span cap L : ℕ)
    (hp : coefficientWordFunction.program.tapeCount ≤ span)
    (support : List ℕ) (coefficient : ℤ) (σ : WState (span+29) 32)
    (blank : CallBlank coefficientWordFunction.program (kernelSite span coefficientWordFunction.program hp) σ)
    (hs : σ.st (kernelLocal span 14)=frame (listWord natWord support))
    (hsh : σ.sh (kernelLocal span 14)=0)
    (hc : σ.st (kernelLocal span 15)=frame (natWord L++intWord coefficient))
    (hch : σ.sh (kernelLocal span 15)=0)
    (hd : σ.st (kernelLocal span 16)=[]) (hdh : σ.sh (kernelLocal span 16)=0)
    (hz : ∀i:Fin 10,σ.val ⟨i.val,by omega⟩=0)
    (h14 : σ.val 14=0) (h15 : σ.val 15=0) (h16 : σ.val 16=0) (h26 : σ.val 26=0)
    (hcap : monomialPrepareCapacity L support coefficient ≤ cap) :
    ∃τ,WXExec cap (monomialPrepareProgram span hp) σ τ (monomialPrepareCost L support coefficient) ∧
      SimW (monomialPrepareState span L support coefficient σ) τ := by
  let q : CoefficientRequest := ⟨L,coefficient⟩
  have part (x : ℕ) (hx : x∈([(frame (listWord natWord support)).length,
      2^(natBitLength support.length+1),support.length,1,4*q.word.length+4,
      2*q.word.length+2+q.budget,q.output.length+1] : List ℕ)) : x ≤ cap :=
    (List.le_sum_of_mem hx).trans hcap
  have hframecap := part (frame (listWord natWord support)).length (by simp)
  have hpowcap := part (2^(natBitLength support.length+1)) (by simp)
  have hmcap := part support.length (by simp)
  have hone := part 1 (by simp)
  have hcopycap := part (4*q.word.length+4) (by simp)
  have hcallcap := part (2*q.word.length+2+q.budget) (by simp)
  have hreplycap := part (q.output.length+1) (by simp)
  have h0 : σ.val (0:Fin 32)=0 := hz ⟨0,by decide⟩
  have h1 : σ.val (1:Fin 32)=0 := hz ⟨1,by decide⟩
  have h2 : σ.val (2:Fin 32)=0 := hz ⟨2,by decide⟩
  have h3 : σ.val (3:Fin 32)=0 := hz ⟨3,by decide⟩
  have h6 : σ.val (6:Fin 32)=0 := hz ⟨6,by decide⟩
  have kl {i j : Fin 30} : kernelLocal span i=kernelLocal span j ↔ i=j :=
    (kernelLocal span).injective.eq_iff
  have e1 := rememberFrameProgram_spec cap (kernelLocal span 14) (kernelLocal span 28) 1 26 6 0
    (by simp [kl]) (by decide) (by decide) (by decide) (by decide)
    (listWord natWord support) σ hs hsh
    (by
      change σ.sh (kernelSite span coefficientWordFunction.program hp).guard=
        (σ.st (kernelSite span coefficientWordFunction.program hp).guard).length
      rw [blank.guardHead,blank.guard]
      rfl)
    (by rw [h0];omega) h1 h26 h6 hframecap
  let a := σ.setv 26 (frame (listWord natWord support)).length
  have e2 := readNatM_spec cap true (kernelLocal span 14) (0:Fin 32) 1 16 2 3
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) support.length []
      (frame (support.flatMap natWord)) a
    (by simp [a,hs,NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc,listWord,
      NearCubicGates.Close.Codec.frame_eq_marks,NearCubicWires.RepairOrdinary.Streaming.marks,List.flatMap_append,List.append_assoc])
    (by simp [a,hsh]) (by simp [a,h0]) (by simp [a,h1])
    (by simp [a,h2]) (by simp [a,h3]) (by simpa only [a,WState.setv_val,Function.update_of_ne (by decide : (16:Fin 32)≠26),h16,Nat.zero_add] using hpowcap)
  let b := (a.seth (kernelLocal span 14) (marks (natWord support.length)).length).setv 16 support.length
  have e2' : WExec cap (readNatM true (kernelLocal span 14) 0 1 16 2 3) a b
      (scalarReadCost support.length) := by
    simpa [b,stp,a,h16,scalarReadCost] using e2
  have e3 := wcopyR_spec cap (16:Fin 32) 15 6 (by decide) (by decide) (by decide) b
    (by simp [b,a,h15]) (by simp [b,a,h6]) (by simpa only [b,WState.setv_val,Function.update_self] using hmcap)
  let c := b.setv 15 support.length
  have e3' : WExec cap (wcopyR (16:Fin 32) 15 6) b c (18*support.length+3) := by
    simpa [c,b] using e3
  have e4 := WExec.inc (cap:=cap) (14:Fin 32) c (by simp [c,b,a,h14];omega)
  let d := c.setv 14 1
  have e4' : WExec cap (.inc (14:Fin 32)) c d 3 := by simpa [d,c,b,a,h14] using e4
  let s := kernelSite span coefficientWordFunction.program hp
  have hb : CallBlank coefficientWordFunction.program s d := by
    have hh (R : Fin 32) (hR : R=26 ∨ R=16 ∨ R=15 ∨ R=14) : ∀i,s.regs i≠R := by
      intro i;fin_cases i <;> rcases hR with rfl|rfl|rfl|rfl <;> simp [s,kernelSite,kernelCallRegisters]
    exact (((((blank.setv 26 _ (hh 26 (by simp))).seth (kernelLocal span 14) _
      (kernelSite_out span _ hp 14 (by decide) (by decide))
      (kernelSite_ruler_ne span _ hp 14 (by decide))).setv 16 _ (hh 16 (by simp))).setv 15 _
      (hh 15 (by simp))).setv 14 _ (hh 14 (by simp)))
  obtain ⟨τ,et,ht⟩ := cachedCallProgram_spec coefficientWordFunction
    (CoefficientRequest.mk L coefficient) cap s (kernelLocal span 15) (kernelLocal span 16) 0 1 2
    (by intro he;have hv:=congrArg Fin.val he;change 15=30 at hv;omega)
    (by decide) (by decide) (by decide)
    (kernelSite_out span _ hp 16 (by decide) (by decide))
    (kernelSite_ruler_ne span _ hp 16 (by decide)) (by simp [s,kernelSite,kernelCallRegisters])
    d hb (by simpa [d,c,b,a,CoefficientRequest.word] using hc)
    (by simp [d,c,b,a,hch]) (by simp [d,c,b,a,hd]) (by simp [d,c,b,a,hdh])
    (by simp [d,c,b,a,h0]) (by simp [d,c,b,a,h1]) (by simp [d,c,b,a,h2])
    hcopycap hcallcap hreplycap
  refine ⟨τ,?_,?_⟩
  · simpa only [monomialPrepareProgram,monomialPrepareCost,CoefficientRequest.output,s] using
      (WXExec.wm e1).seq ((WXExec.wm e2').seq ((WXExec.wm e3').seq ((WXExec.wm e4').seq et)))
  · exact ht

end NearQuarticWires.StageTuple
