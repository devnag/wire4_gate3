import Proof.Quartic.StagePrintTuple.CartesianInput
import Proof.Quartic.StagePrintTuple.CartesianReply
import Proof.Quartic.StagePrintTuple.CallInput

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearCubicGates.Close.WorkerArith (inTape)
open NearQuarticWires.Control

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: a complete
Cartesian child step physically formats its real current inputs,
advances only the current history segment, calls the genuine Cartesian
machine and selects the newly appended tuple segment. -/
noncomputable def cartesianStepProgram (P : Fin 3 ↪ Fin (ns+1)) (R : Fin 8 ↪ Fin nr)
    (s : Site tupleRecordPrinter.program ns nr) : WMX ns nr :=
  .seq (.wm (cartesianInputProgram P R))
    (.seq (.wm (advanceRecordHistory (P 1) (R 1))) (cartesianReplyProgram s (P 1) (R 0)))

/-- `prop:time`, paper/paper.tex: the full
Cartesian step adds actual input formatting, current-history scanning
and the genuine callee clock, without a history-prefix multiplier. -/
def cartesianStepCost (r : StagePrint.ChildTupleRequest) : ℕ :=
  cartesianInputCost r+40*(((fieldRecords r.L r.tuples).flatMap frame).length+1)+
    cartesianReplyCost r+2

/-- `lem:print` and `prop:time`, paper/paper.tex: one complete physical Cartesian step consumes actual
original children and suffix tuple bytes and emits the exact new tuple
segment. Its request is constructed on a blank call bank; no compiled
input, tuple reply or output-count oracle is an input premise. -/
theorem cartesianStepProgram_spec (cap : ℕ) (P : Fin 3 ↪ Fin (ns+1)) (R : Fin 8 ↪ Fin nr)
    (s : Site tupleRecordPrinter.program ns nr) (hi : P 2=s.input)
    (r : StagePrint.ChildTupleRequest) (preK preT : List Bool) (σ : WState ns nr)
    (blank : CallBlank tupleRecordPrinter.program s σ)
    (hout : s.Out (P 1)) (hL : P 1≠s.ruler) (hOS : R 0≠s.regs 0)
    (hk : σ.st (P 0)=preK++(fieldRecords r.L r.children).flatMap frame)
    (ht : σ.st (P 1)=preT++(fieldRecords r.L r.tuples).flatMap frame++[false])
    (hkh : σ.sh (P 0)=preK.length) (hth : σ.sh (P 1)=preT.length)
    (hz : ∀i:Fin 4,σ.val (R (Fin.castAdd 4 i))=0)
    (hv : [R 4,R 5,R 6,R 7].map σ.val=[r.N,r.M,r.children.length,r.tuples.length])
    (hcap : 400*((fieldRecords r.L r.children).flatMap frame |>.length)+
      400*((fieldRecords r.L r.tuples).flatMap frame |>.length)+
      400*(r.N+r.M+r.children.length+r.tuples.length+10)≤cap)
    (hcall : 2*r.word.length+2+(2*r.budget+2)≤cap)
    (hreply : ((tupleRecords r).flatMap frame).length+1≤cap) :
    ∃τ,WXExec cap (cartesianStepProgram P R s) σ τ (cartesianStepCost r) ∧
      SimW (closedHistory σ (P 1) (R 0) (σ.st (P 1)) ((tupleRecords r).flatMap frame)) τ := by
  have hp {i j:Fin 3} : P i=P j ↔ i=j := P.injective.eq_iff
  have hr {i j:Fin 8} : R i=R j ↔ i=j := R.injective.eq_iff
  have h0 : σ.val (R 0)=0 := hz 0
  have h1 : σ.val (R 1)=0 := hz 1
  have h2 : σ.val (R 2)=0 := hz 2
  have e1 := cartesianInputProgram_spec cap P R r preK preT [] [false] (by rfl) (by rfl) σ
    (by simpa using hk) ht hkh hth
    (by rw [hi];exact blank.bank (inTape tupleRecordPrinter.program))
    (by rw [hi];exact blank.heads (inTape tupleRecordPrinter.program)) hz hv hcap
  let a := σ.sets (P 2) (frame r.word)
  have hgi : s.guard≠P 2 := by
    rw [hi]
    exact (s.guard_ne (inTape tupleRecordPrinter.program)).symm
  have e2 := advanceRecordHistory_spec cap (P 1) s.guard (R 1) (R 2)
    hout.2.2 (R.injective.ne (by decide)) (fieldRecords r.L r.tuples) preT
    (fieldRecords_nonempty r.L r.width_pos _) a
    (by simp [a,hp,ht]) (by simp [a,hth])
    (by simp [a,hgi,blank.guard,blank.guardHead])
    (by simp [a,h2]) (by simp [a,h1]) (by omega)
  let b := a.seth (P 1) (a.st (P 1)).length
  let base := σ.seth (P 1) (σ.st (P 1)).length
  have hb : b=base.sets s.input (frame r.word) := by
    rw [←hi]
    apply WState.eq
    · simp [b,base,a,hp]
    · rfl
    · rfl
    · rfl
  have bblank : CallBlank tupleRecordPrinter.program s base :=
    blank.seth (P 1) _ hout hL
  have ready : CallReady tupleRecordPrinter.program s r.word b := by
    rw [hb]
    exact bblank.ready r.word
  have bh : b.sh (P 1)=(b.st (P 1)).length := by simp [b]
  obtain ⟨c,ec,hc⟩ := cartesianReplyProgram_spec cap r s (P 1) (R 0) hout hL hOS b ready bh
    (by simp [b,a,h0]) hcall hreply
  have clean : cleanState s b=base := by
    rw [hb,Site.input,StagePrint.cleanState_set_bank]
    exact bblank.clean
  have bs : b.st (P 1)=σ.st (P 1) := by simp [b,a,hp]
  rw [clean,bs] at hc
  have hpost : closedHistory (appendO base (P 1) (R 0) ((tupleRecords r).flatMap frame))
      (P 1) (R 0) (σ.st (P 1)) ((tupleRecords r).flatMap frame)=
      closedHistory σ (P 1) (R 0) (σ.st (P 1)) ((tupleRecords r).flatMap frame) := by
    apply WState.eq
    · funext i
      by_cases hh:i=P 1
      · subst i;simp [closedHistory,base,appendO]
      · simp [closedHistory,base,appendO,Function.update_of_ne hh]
    · funext i
      by_cases hh:i=P 1
      · subst i;simp [closedHistory]
      · simp [closedHistory,base,appendO,Function.update_of_ne hh]
    · funext i
      by_cases hh:i=R 0
      · subst i;simp [closedHistory]
      · simp [closedHistory,base,appendO,Function.update_of_ne hh]
    · rfl
  rw [hpost] at hc
  exact ⟨c,((WXExec.wm e1).seq ((WXExec.wm e2).seq ec)).mono
    (by unfold cartesianStepCost;omega),hc⟩

end NearQuarticWires.StageTuple
