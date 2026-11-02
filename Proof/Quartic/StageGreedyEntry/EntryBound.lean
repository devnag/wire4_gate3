import Proof.Quartic.StageGreedyEntry.Entry
import Proof.Quartic.StageGreedyEntry.ModularInput

/-!
# The per-entry producer and its selected clock

Paper: `lem:print`, `lem:residue` and `prop:time`, paper/paper.tex.

`entryProducerWith tuple` is the whole actual per-entry chain with the physical modular-input stage.
`entryProducerWith_bound` proves the selected per-entry clock from the selected clock of the tuple
program on actual entries: every stage is linear in the word it reads, which is shorter than the clock
of the stage that wrote it, plus a polynomial in the original arity, except the per-walk square of the
equality-row constructor (`equality_ebb`).
-/

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyEntry

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Expand.PolyTab
open StagePrint StageGreedyCollector StageCertificateControl

variable (B1 B2 : ℕ)

/-- `lem:residue` and `lem:print`, paper/paper.tex: the actual
modular-cut input from the retained naturals and the signed weak stream. -/
noncomputable def modularInputStage :
    ModularInputStage B1 B2 (fun r=>2*modInCost (natWord (wd r)++(natWord r.modulus++
      (natWord r.termRequest.stackWidth++(modularRequest r).stream))).length (wd r) r.termRequest.stackWidth+2) :=
  recast (wordFunction_of_ideal (.wm modInP) 1 (by decide)
    (fun r : GreedyEntry.Request B1 B2=>10*((natWord (wd r)++(natWord r.modulus++
      (natWord r.termRequest.stackWidth++(modularRequest r).stream))).length+1)+8*(wd r+r.termRequest.stackWidth+4))
    (fun _ _=>0)
    (fun r=>modInCost (natWord (wd r)++(natWord r.modulus++
      (natWord r.termRequest.stackWidth++(modularRequest r).stream))).length (wd r) r.termRequest.stackWidth)
    (fun _=>le_rfl)
    (fun r=>⟨rfl,modInP_run (wd r) r.modulus r.termRequest.stackWidth (modularRequest r).stream |>.elim
      fun τ h=>⟨τ,WXExec.wm h.1,h.2⟩⟩))
    (fun _=>rfl)
    (fun r=>by
      show frame (Top.loadRec _ _ _ _ [] [] [] [] [] [] [])=frame (Downstream.ModularCutsRequest.word _)
      unfold Downstream.ModularCutsRequest.word
      rw [show (modularRequest r).width=wd r from wd_eq r]
      rfl)
    (fun _=>le_rfl)

/-- `lem:print`, paper/paper.tex: the whole per-entry producer, given the tuple program. -/
noncomputable def entryProducerWith {tb : StageTuple.TermCutRequest→ℕ}
    (tuple : WordFunction StageTuple.TermCutRequest StageTuple.TermCutRequest.word (fun t=>frame t.output) tb) :
    EntryProducer B1 B2 :=
  entryProducerOf B1 B2 tuple (modularInputStage B1 B2)

variable {B1 B2}

theorem sq_arity (B1 B2 : ℕ) : ∃K e : ℕ,∀r : GreedyEntry.Request B1 B2,
    (wd r+r.termRequest.stackWidth+natBitLength r.modulus+2)^20≤K*(r.source.child.call.n+1)^e := by
  obtain ⟨K,e,hK⟩:=scale_arity B1 B2
  exact ⟨K^20,20*e,fun r=>(Nat.pow_le_pow_left (hK r) 20).trans (le_of_eq (by ring))⟩

/-- A square of the small widths, bounded by the twentieth power above. -/
theorem sq2_ebb (B1 B2 : ℕ) : EntryBudgetBound (fun r : GreedyEntry.Request B1 B2=>
    (wd r+r.termRequest.stackWidth+2)^2) := by
  obtain ⟨K,e,hK⟩:=sq_arity B1 B2
  refine ebb_of_arity ⟨K,e,fun r=>le_trans ?_ (hK r)⟩
  have h1 : wd r+r.termRequest.stackWidth+2≤wd r+r.termRequest.stackWidth+natBitLength r.modulus+2 := by omega
  calc
    _≤(wd r+r.termRequest.stackWidth+natBitLength r.modulus+2)^2 := Nat.pow_le_pow_left h1 2
    _≤_ := Nat.pow_le_pow_right (by omega) (by decide)

theorem stage1_ebb (B1 B2 : ℕ) : EntryBudgetBound (fun r : GreedyEntry.Request B1 B2=>
    2*prefixCost (EntryFormat.ofGreedy r).word.length r.source.child.call.n+2) := by
  refine ebb_mono (ebb_add (ebb_smul (word_ebb B1 B2) 2000) (ebb_arity (3*10^4) 2)) (fun r=>?_)
  have h : 1≤(r.source.child.call.n+1)^2 := Nat.one_le_pow _ _ (by omega)
  unfold prefixCost
  generalize (r.source.child.call.n+1)^2=N at h ⊢
  omega

theorem tw_ebb (B1 B2 : ℕ) : EntryBudgetBound (fun r : GreedyEntry.Request B1 B2=>r.termRequest.word.length) :=
  ebb_mono (formatter_bound B1 B2) (framed_length_le (formatter B1 B2))

theorem stage2_ebb (B1 B2 : ℕ) : EntryBudgetBound (fun r : GreedyEntry.Request B1 B2=>
    nativePrefixBudget (wd r) (natWord r.modulus++(EntryFormat.ofGreedy r).word).length
      (nativePrefixBudget r.modulus (EntryFormat.ofGreedy r).word.length (formatterBudget B1 B2 r))) :=
  ebb_prefix (natWord_wd_ebb B1 B2)
    (ebb_mono (ebb_add (natWord_modulus_ebb B1 B2) (word_ebb B1 B2)) (fun r=>by simp))
    (ebb_prefix (natWord_modulus_ebb B1 B2) (word_ebb B1 B2) (formatter_bound B1 B2))

theorem stage3_ebb (B1 B2 : ℕ) : EntryBudgetBound (fun r : GreedyEntry.Request B1 B2=>
    2*stackCost (natWord (wd r)++(natWord r.modulus++r.termRequest.word)).length+2) :=
  ebb_mono (ebb_add (ebb_smul (stage2_ebb B1 B2) 2000) (ebb_const 2002)) (fun r=>by
    have h:=framed_length_le (formatStage B1 B2) r
    unfold stackCost

    omega)

theorem stage4_ebb (B1 B2 : ℕ) {tb : StageTuple.TermCutRequest→ℕ}
    (htb : EntryBudgetBound (fun r : GreedyEntry.Request B1 B2=>tb r.termRequest)) :
    EntryBudgetBound (fun r : GreedyEntry.Request B1 B2=>
      nativePrefixBudget (wd r) (natWord r.modulus++(natWord r.termRequest.stackWidth++r.termRequest.word)).length
        (nativePrefixBudget r.modulus (natWord r.termRequest.stackWidth++r.termRequest.word).length
          (nativePrefixBudget r.termRequest.stackWidth r.termRequest.word.length (tb r.termRequest)))) :=
  ebb_prefix (natWord_wd_ebb B1 B2)
    (ebb_mono (ebb_add (ebb_add (natWord_modulus_ebb B1 B2) (natWord_stack_ebb B1 B2)) (tw_ebb B1 B2))
      (fun r=>by simp;omega))
    (ebb_prefix (natWord_modulus_ebb B1 B2)
      (ebb_mono (ebb_add (natWord_stack_ebb B1 B2) (tw_ebb B1 B2)) (fun r=>by simp))
      (ebb_prefix (natWord_stack_ebb B1 B2) (tw_ebb B1 B2) htb))

theorem stage5_ebb (B1 B2 : ℕ) {tb : StageTuple.TermCutRequest→ℕ}
    (tuple : WordFunction StageTuple.TermCutRequest StageTuple.TermCutRequest.word (fun t=>frame t.output) tb)
    (htb : EntryBudgetBound (fun r : GreedyEntry.Request B1 B2=>tb r.termRequest)) :
    EntryBudgetBound (fun r : GreedyEntry.Request B1 B2=>
      2*rowsCost (natWord (wd r)++(natWord r.modulus++(natWord r.termRequest.stackWidth++
        r.termRequest.output))).length (wd r) r.termRequest.stackWidth+2) :=
  ebb_mono (ebb_add (ebb_add (ebb_smul (stage4_ebb B1 B2 htb) 2000) (ebb_smul (sq2_ebb B1 B2) (2*10^4)))
    (ebb_const 2002)) (fun r=>by
      have h:=framed_length_le (tupleStage B1 B2 tuple) r
      have h2 : (wd r+r.termRequest.stackWidth+1)^2≤(wd r+r.termRequest.stackWidth+2)^2 :=
        Nat.pow_le_pow_left (by omega) 2
      unfold rowsCost
      generalize (wd r+r.termRequest.stackWidth+1)^2=X at h2 ⊢
      generalize (wd r+r.termRequest.stackWidth+2)^2=Y at h2 ⊢
      omega)

theorem stage6_ebb (B1 B2 : ℕ) {tb : StageTuple.TermCutRequest→ℕ}
    (tuple : WordFunction StageTuple.TermCutRequest StageTuple.TermCutRequest.word (fun t=>frame t.output) tb)
    (htb : EntryBudgetBound (fun r : GreedyEntry.Request B1 B2=>tb r.termRequest)) :
    EntryBudgetBound (fun r : GreedyEntry.Request B1 B2=>
      nativePrefixBudget (wd r) (natWord r.modulus++(natWord r.termRequest.stackWidth++
          Downstream.equalityRowsInput (equalityRequest r))).length
        (nativePrefixBudget r.modulus (natWord r.termRequest.stackWidth++
            Downstream.equalityRowsInput (equalityRequest r)).length
          (nativePrefixBudget r.termRequest.stackWidth (Downstream.equalityRowsInput (equalityRequest r)).length
            (10^30*(PrimT.C4Geo.width (equalityRequest r).parameters+(equalityRequest r).fieldWidth+2)^20*
              (((equalityRequest r).cuts.flatMap
                (MatrixScoreBatch.cutWord (equalityRequest r).fieldWidth)).length+1)^2)))) := by
  have h5:=stage5_ebb B1 B2 tuple htb
  have hl (r : GreedyEntry.Request B1 B2):=framed_length_le (rowsStage B1 B2) r
  exact ebb_prefix (natWord_wd_ebb B1 B2) (ebb_mono h5 (fun r=>by have:=hl r;simp at this ⊢;omega))
    (ebb_prefix (natWord_modulus_ebb B1 B2) (ebb_mono h5 (fun r=>by have:=hl r;simp at this ⊢;omega))
      (ebb_prefix (natWord_stack_ebb B1 B2) (ebb_mono h5 (fun r=>by have:=hl r;simp at this ⊢;omega))
        (equality_ebb B1 B2)))

theorem stage7_ebb (B1 B2 : ℕ) {tb : StageTuple.TermCutRequest→ℕ}
    (tuple : WordFunction StageTuple.TermCutRequest StageTuple.TermCutRequest.word (fun t=>frame t.output) tb)
    (htb : EntryBudgetBound (fun r : GreedyEntry.Request B1 B2=>tb r.termRequest)) :
    EntryBudgetBound (fun r : GreedyEntry.Request B1 B2=>2*modInCost (natWord (wd r)++(natWord r.modulus++
      (natWord r.termRequest.stackWidth++(modularRequest r).stream))).length (wd r) r.termRequest.stackWidth+2) :=
  ebb_mono (ebb_add (ebb_add (ebb_smul (stage6_ebb B1 B2 tuple htb) 2000) (ebb_smul (sq2_ebb B1 B2) (2*10^4)))
    (ebb_const 2002)) (fun r=>by
      have h : (natWord (wd r)++(natWord r.modulus++(natWord r.termRequest.stackWidth++
          (modularRequest r).stream))).length≤_ := framed_length_le (equalityStage B1 B2) r
      unfold modInCost
      generalize (wd r+r.termRequest.stackWidth+2)^2=Y
      omega)

theorem stage8_ebb (B1 B2 : ℕ) {tb : StageTuple.TermCutRequest→ℕ}
    (tuple : WordFunction StageTuple.TermCutRequest StageTuple.TermCutRequest.word (fun t=>frame t.output) tb)
    (htb : EntryBudgetBound (fun r : GreedyEntry.Request B1 B2=>tb r.termRequest)) :
    EntryBudgetBound (fun r : GreedyEntry.Request B1 B2=>
      10^30*((modularRequest r).width+(modularRequest r).fieldWidth+natBitLength (modularRequest r).modulus+2)^20*
        ((modularRequest r).stream.length+1)) := by
  obtain ⟨K,e,hK⟩:=sq_arity B1 B2
  refine ebb_mono (ebb_mul_arity (ebb_add (stage6_ebb B1 B2 tuple htb) (ebb_const 1)) (10^30*2^20*K) e)
    (fun r=>?_)
  have h : (natWord (wd r)++(natWord r.modulus++(natWord r.termRequest.stackWidth++
      (modularRequest r).stream))).length≤_ := framed_length_le (equalityStage B1 B2) r
  have hs : (modularRequest r).stream.length≤(natWord (wd r)++(natWord r.modulus++(natWord r.termRequest.stackWidth++
      (modularRequest r).stream))).length := by simp only [List.length_append];omega
  have hw : (modularRequest r).width=wd r := wd_eq r
  have hS : (modularRequest r).width+(modularRequest r).fieldWidth+natBitLength (modularRequest r).modulus+2≤
      2*(wd r+r.termRequest.stackWidth+natBitLength r.modulus+2) := by
    rw [hw];change wd r+(r.termRequest.stackWidth+1)+natBitLength r.modulus+2≤_;omega
  have h20 : ((modularRequest r).width+(modularRequest r).fieldWidth+natBitLength (modularRequest r).modulus+2)^20≤
      2^20*(K*(r.source.child.call.n+1)^e) :=
    (Nat.pow_le_pow_left hS 20).trans (by rw [mul_pow];exact Nat.mul_le_mul_left _ (hK r))
  calc
    _≤10^30*(2^20*(K*(r.source.child.call.n+1)^e))*((modularRequest r).stream.length+1) := by gcongr
    _≤10^30*(2^20*(K*(r.source.child.call.n+1)^e))*
        (nativePrefixBudget (wd r) (natWord r.modulus++(natWord r.termRequest.stackWidth++
          Downstream.equalityRowsInput (equalityRequest r))).length
        (nativePrefixBudget r.modulus (natWord r.termRequest.stackWidth++
            Downstream.equalityRowsInput (equalityRequest r)).length
          (nativePrefixBudget r.termRequest.stackWidth (Downstream.equalityRowsInput (equalityRequest r)).length
            (10^30*(PrimT.C4Geo.width (equalityRequest r).parameters+(equalityRequest r).fieldWidth+2)^20*
              (((equalityRequest r).cuts.flatMap
                (MatrixScoreBatch.cutWord (equalityRequest r).fieldWidth)).length+1)^2)))+1) := by
      gcongr;omega
    _=_ := by ring

/-- `prop:time`, paper/paper.tex: the selected per-entry clock of the whole chain. -/
theorem entryProducerWith_bound (B1 B2 : ℕ) {tb : StageTuple.TermCutRequest→ℕ}
    (tuple : WordFunction StageTuple.TermCutRequest StageTuple.TermCutRequest.word (fun t=>frame t.output) tb)
    (htb : EntryBudgetBound (fun r : GreedyEntry.Request B1 B2=>tb r.termRequest)) :
    EntryBudgetBound (entryProducerWith B1 B2 tuple).1 :=
  ebb_pipe (ebb_pipe (ebb_pipe (ebb_pipe (ebb_pipe (ebb_pipe (ebb_pipe (stage1_ebb B1 B2) (stage2_ebb B1 B2))
    (stage3_ebb B1 B2)) (stage4_ebb B1 B2 htb)) (stage5_ebb B1 B2 tuple htb)) (stage6_ebb B1 B2 tuple htb))
    (stage7_ebb B1 B2 tuple htb)) (stage8_ebb B1 B2 tuple htb)

end NearQuarticWires.StageGreedyEntry
