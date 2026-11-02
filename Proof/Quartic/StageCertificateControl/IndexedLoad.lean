import Proof.Quartic.StageCertificateControl.IndexedLayout

/-!
# Cold indexed input to the actual prepared scheduler bank

Paper: Step 2 of `sec:algorithm`, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks marks_length marks_append)
open NearCubicGates.Close NearCubicGates.Close.Interfaces NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.WorkerArith (inTape)
open NearQuarticWires.Control

/-- `prop:time`, paper/paper.tex: the
index is physically decoded into its own register, while the original
source head remains at the actual preparation offset. -/
noncomputable def indexedReadState {B1 B2 : ℕ} (p : Program) (r : IndexedRequest B1 B2) :
    WState (p.tapeCount+11) 32 :=
  ((startState (p.tapeCount+11) 32 r.word).seth (indexedExternal p 0)
    (2*(RepairRepresentation.natWord r.index.val).length)).setv 4 r.index.val

/-- `prop:time`, paper/paper.tex: the
real scheduler input is a measured physical preparation copy at head
zero, and the original index and preparation source remain retained. -/
noncomputable def indexedLoadedState {B1 B2 : ℕ} (p : Program) (r : IndexedRequest B1 B2) :
    WState (p.tapeCount+11) 32 :=
  (((indexedReadState p r).sets (indexedSite p).input (frame r.prepared.word)).seth
    (indexedSite p).input 0).setv 21 (2*r.prepared.word.length)

/-- `prop:time`, paper/paper.tex: the
cold indexed load pays the actual bounded numeric-index parser and
only a linear number of instructions in preparation bytes. -/
noncomputable def indexedLoadCost {B1 B2 : ℕ} (r : IndexedRequest B1 B2) : ℕ :=
  (natBitLength r.index.val+2)*(40*2^natBitLength r.index.val+40)+
    (200*r.prepared.word.length+100)+1

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: the literal indexed source produces the
actual cold scheduler-bank input, without supplied decoded metadata,
a source-offset reset, or a threshold numeric-value allocation. -/
theorem indexedLoad_exec {B1 B2 : ℕ} (p : Program) (r : IndexedRequest B1 B2) (cap : ℕ)
    (hindex : 2^(natBitLength r.index.val+1)≤cap) (hcopy : 4*r.prepared.word.length+4≤cap) :
    WXExec cap (indexedLoadProgram p) (startState (p.tapeCount+11) 32 r.word)
      (indexedLoadedState p r) (indexedLoadCost r) := by
  let S := indexedExternal p 0
  let σ := startState (p.tapeCount+11) 32 r.word
  have hsplit : frame r.word=marks (RepairRepresentation.natWord r.index.val)++frame r.prepared.word := by
    simp [IndexedRequest.word,Codec.frame_eq_marks,NearCubicWires.RepairOrdinary.Streaming.marks_append,List.append_assoc]
  have er := readNatM_spec cap true S (0 : Fin 32) 1 4 2 3
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    r.index.val [] (frame r.prepared.word) σ
    (by change frame r.word=_;simpa [NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc] using hsplit) rfl rfl rfl rfl rfl
    (by simpa [σ,startState] using hindex)
  have he : (σ.seth S (([] : List Bool).length+stp true*
      (RepairRepresentation.natWord r.index.val).length)).setv 4 (σ.val 4+r.index.val)=
      indexedReadState p r := by simp [σ,S,indexedReadState,stp,startState]
  rw [he] at er
  let a := indexedReadState p r
  have hinput : (indexedSite p).input≠S := indexedBank_external_ne p (inTape p) 0
  have hval : ((indexedSite p).input).val≠0 := by change 11+(inTape p).val≠0;omega
  have ec := copyPreparation_spec cap S (indexedSite p).input hinput.symm indexedPreparationRegs
    r.prepared.word a
    (by
      intro q
      change readTapeBit (frame r.word) (2*(RepairRepresentation.natWord r.index.val).length+q)=_
      rw [hsplit]
      unfold readTapeBit
      rw [List.getD_append_right _ _ _ _ (by simp [marks_length])]
      simp [marks_length])
    (by change (if ((indexedSite p).input).val=0 then frame r.word else [])=[];rw [if_neg hval])
    (by simp [a,indexedReadState,S,Function.update_of_ne hinput,startState])
    (by intro i;fin_cases i <;> rfl) hcopy
  exact (WXExec.seq (WXExec.wm er) ec).mono (by unfold indexedLoadCost;omega)

/-- `prop:time`, paper/paper.tex: every
actual scheduler-bank tape is initialized with the real preparation
input, and every physical bank head is zero. -/
theorem indexedLoadedState_bank {B1 B2 : ℕ} (p : Program) (r : IndexedRequest B1 B2) :
    (∀ j,(indexedLoadedState p r).st (indexedBank p j)=p.inputTapes r.prepared.word j) ∧
      (∀ j,(indexedLoadedState p r).sh (indexedBank p j)=0) := by
  have hne (j : Fin p.tapeCount) := indexedBank_external_ne p j 0
  constructor
  · intro j
    by_cases hj : j=inTape p
    · subst j;simp [indexedLoadedState,Site.input,indexedSite,Program.inputTapes,inTape]
    · have hji : indexedBank p j≠(indexedSite p).input := by
        intro h
        apply hj
        exact (indexedSite p).bank_inj h
      have hjv : j.val≠0 := by intro h;apply hj;apply Fin.ext;exact h
      have hv : (indexedBank p j).val≠0 := by change 11+j.val≠0;omega
      have hb : indexedBank p j≠(0 : Fin (p.tapeCount+12)) := by
        intro h;exact hv (congrArg Fin.val h)
      simp [indexedLoadedState,indexedReadState,Function.update_of_ne hji,
        startState,Program.inputTapes,hjv,hv,hb]
  · intro j
    by_cases hj : indexedBank p j=(indexedSite p).input
    · simp [indexedLoadedState,hj]
    · simp [indexedLoadedState,indexedReadState,Function.update_of_ne hj,Function.update_of_ne (hne j),startState]

end NearQuarticWires.StageCertificateControl
