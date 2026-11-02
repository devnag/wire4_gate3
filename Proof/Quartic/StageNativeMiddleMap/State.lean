import Proof.Quartic.StageNativeMiddleMap.Layout

set_option autoImplicit false

namespace NearQuarticWires.StageNativeMiddleMap

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearCubicGates.Close.WorkerArith (inTape)
open NearQuarticWires.Control

theorem loaded_external (p : Program) (cap q : ℕ) (input : List Bool) (count : ℕ) (i : Fin 19) :
    (loaded p cap q input count).st (external p i)=
      (if h : i.val<13 then fields q input count ⟨i.val,h⟩
       else if i.val=13 then List.replicate cap false else []) := rfl

theorem loaded_bank (p : Program) (cap q : ℕ) (input : List Bool) (count : ℕ) (j : Fin p.tapeCount) :
    (loaded p cap q input count).st (bank p j)=[] := by
  simp [loaded,bank,show ¬19+j.val<13 by omega,show 19+j.val≠13 by omega]

/-- `lem:print`, paper/paper.tex: the
genuine isolated middle frame is the actual cold input of the fixed
callee, and every other physical bank tape is initially blank. -/
theorem prepared_bank (p : Program) (cap q : ℕ) (input : List Bool) (count : ℕ) :
    (∀ j,(prepared p cap q input count).st (bank p j)=p.inputTapes input j) ∧
      (∀ j,(prepared p cap q input count).sh (bank p j)=0) := by
  constructor
  · intro j
    by_cases hj : j=inTape p
    · subst j
      simp [prepared,site,Site.input,Program.inputTapes,inTape]
    · have hne : bank p j≠(site p).input := (bank_injective p).ne hj
      have hjv : j.val≠0 := by intro h;apply hj;exact Fin.ext h
      simp [prepared,Function.update_of_ne hne,loaded_bank,Program.inputTapes,hjv]
  · intro j
    rfl

theorem clean_prepared (p : Program) (cap q : ℕ) (input : List Bool) (count : ℕ) :
    cleanState (site p) (prepared p cap q input count)=loaded p cap q input count := by
  change cleanState (site p)
    ((loaded p cap q input count).sets ((site p).bank (inTape p)) (frame input))=_
  rw [StagePrint.cleanState_set_bank]
  apply StagePrint.cleanState_self
  · exact loaded_bank p cap q input count
  · intro j;rfl
  · rfl
  · rfl

theorem callPost_eq (p : Program) (cap q : ℕ) (input output : List Bool) (count : ℕ)
    (tapes : Fin p.tapeCount→List Bool) (steps : ℕ) :
    cleanState (site p) (appendO (calledState (site p) (prepared p cap q input count)
      tapes input.length steps) (external p 18) (6 : Fin 32) (frame output))=
      copied p cap q input output count := by
  rw [StagePrint.callAppendPost_eq (site p) _ tapes input.length steps (external p 18) 6 (frame output)
    (fun j=>bank_external_ne p j 18)
    ((external_injective p).ne (by decide)) ((external_injective p).ne (by decide))]
  rw [clean_prepared]
  rfl

theorem ready_fields (p : Program) (cap q : ℕ) (input output : List Bool) (count : ℕ) :
    let a:=ready p cap q input output count
    a.st (external p 2)=NearCubicWires.RepairRepresentation.natWord q ∧
      a.st (external p 4)=NearCubicWires.RepairRepresentation.natWord count ∧
      a.st (external p 18)=frame output ∧ a.st (external p 17)=[] ∧
      a.st (final p)=[] ∧ (∀ i,a.sh i=0) ∧ (∀ i,a.val i=0) := by
  dsimp only
  and_intros
  all_goals simp [ready,copied,appendO,loaded,external,final,fields]

end NearQuarticWires.StageNativeMiddleMap
