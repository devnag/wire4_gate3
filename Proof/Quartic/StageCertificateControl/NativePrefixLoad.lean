import Proof.Quartic.StageCertificateControl.NativePrefixLayout

/-!
# Cold binary threshold retention and actual native-bank input copying

Paper: `eq:testX`–`eq:testPhi`, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.CopyNat
open NearCubicWires.RepairOrdinary.Streaming (marks marks_length)
open NearCubicGates.Close NearCubicGates.Close.Interfaces NearCubicGates.Close.WordPrograms

/-- `prop:time`, paper/paper.tex: the
binary threshold is retained on a separate framed tape while the
original source remains at the literal base-input offset. -/
def nativePrefixReadState (p : Program) (threshold : ℕ) (input : List Bool) :
    WState (p.tapeCount+11) 32 :=
  (((startState (p.tapeCount+11) 32 (RepairRepresentation.natWord threshold++input)).seth
    (indexedExternal p 0) (2*(RepairRepresentation.natWord threshold).length)).sets
      (indexedExternal p 1) (frame (RepairRepresentation.natWord threshold))).setv 4
        (2*(RepairRepresentation.natWord threshold).length)

/-- `prop:time`, paper/paper.tex: the
actual native input bank receives only the unchanged base input;
the binary threshold header and original input remain outside it. -/
def nativePrefixLoadedState (p : Program) (threshold : ℕ) (input : List Bool) :
    WState (p.tapeCount+11) 32 :=
  (((nativePrefixReadState p threshold input).sets (indexedSite p).input (frame input)).seth
    (indexedSite p).input 0).setv 7 (2*input.length)

/-- `eq:testX`–`eq:testPhi` and `prop:time`, paper/paper.tex: the first field is copied by
its actual binary codec, never decoded into a unary threshold-value
register. The exact base-input source offset and real bank copy are
established by charged instructions in linear encoded-byte time. -/
theorem nativePrefixLoad_exec (p : Program) (threshold cap : ℕ) (input : List Bool)
    (hcap : 100*((RepairRepresentation.natWord threshold).length+input.length+1)≤cap) :
    WXExec cap (nativePrefixLoadProgram p)
      (startState (p.tapeCount+11) 32 (RepairRepresentation.natWord threshold++input))
      (nativePrefixLoadedState p threshold input)
      (1000*((RepairRepresentation.natWord threshold).length+input.length+1)) := by
  let S := indexedExternal p 0
  let H := indexedExternal p 1
  let σ := startState (p.tapeCount+11) 32 (RepairRepresentation.natWord threshold++input)
  have hSH : S≠H := by intro h;have hh := congrArg Fin.val h;change 0=1 at hh;omega
  have hsplit : frame (RepairRepresentation.natWord threshold++input)=
      marks (RepairRepresentation.natWord threshold)++frame input := by
    simp [Codec.frame_eq_marks,NearCubicWires.RepairOrdinary.Streaming.marks_append,List.append_assoc]
  have ec := copyNatM_spec cap true S H hSH (0 : Fin 32) 1 4 (by decide) (by decide) (by decide)
    threshold [] (frame input) σ
    (by change frame (RepairRepresentation.natWord threshold++input)=_
        simpa [NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc] using hsplit)
    rfl rfl rfl rfl (by change 0+2*(RepairRepresentation.natWord threshold).length+2≤cap;omega)
  simp only [stp,if_pos trivial,List.length_nil,Nat.zero_add] at ec
  let a := (appendO σ H 4 (marks (RepairRepresentation.natWord threshold))).seth S
    (2*(RepairRepresentation.natWord threshold).length)
  have ef := finishMarkedCopy_spec cap H (4 : Fin 32) 5 6 (by decide) (by decide) (by decide)
    (RepairRepresentation.natWord threshold) a
    (by simp [a,appendO,σ,startState,H,indexedExternal])
    (by simp [a,appendO,hSH.symm,σ,startState,marks_length])
    (by simp [a,appendO,σ,startState,marks_length])
    (by simp [a,appendO,σ,startState]) (by simp [a,appendO,σ,startState]) (by omega)
  have he : (a.sets H (frame (RepairRepresentation.natWord threshold))).seth H 0=
      nativePrefixReadState p threshold input := by
    apply WState.eq
    · funext i
      by_cases hs : i=S
      · subst i;simp [a,appendO,nativePrefixReadState,S,H,hSH,σ,startState]
      · by_cases hh : i=H
        · subst i;simp [nativePrefixReadState,a,appendO,hSH.symm,σ,startState,S,H,indexedExternal]
        · simp [a,appendO,nativePrefixReadState,S,H,Function.update_of_ne hs,Function.update_of_ne hh,σ]
    · funext i
      by_cases hi : i=H
      · subst i;simp [nativePrefixReadState,H]
      · simp [a,appendO,nativePrefixReadState,H,Function.update_of_ne hi,σ]
    · funext i
      by_cases hi : i=4
      · subst i;simp [nativePrefixReadState,a,appendO,σ,startState,marks_length]
      · simp [nativePrefixReadState,a,appendO,σ,Function.update_of_ne hi]
    · rfl
  rw [he] at ef
  let b := nativePrefixReadState p threshold input
  have hbS := indexedBank_external_ne p (NearCubicGates.Close.WorkerArith.inTape p) 0
  have hbH := indexedBank_external_ne p (NearCubicGates.Close.WorkerArith.inTape p) 1
  have hbs : (indexedSite p).input≠indexedExternal p 0 := hbS
  have hbh : (indexedSite p).input≠indexedExternal p 1 := hbH
  have ep := copyPreparation_spec cap S (indexedSite p).input hbS.symm nativePrefixPreparationRegs input b
    (by
      intro q
      change readTapeBit (frame (RepairRepresentation.natWord threshold++input))
        (2*(RepairRepresentation.natWord threshold).length+q)=_
      rw [hsplit]
      unfold readTapeBit
      rw [List.getD_append_right _ _ _ _ (by simp [marks_length])]
      simp [marks_length])
    (by
      have hv : ((indexedSite p).input).val≠0 := by change 11+(NearCubicGates.Close.WorkerArith.inTape p).val≠0;omega
      have hb0 : (indexedSite p).input≠(0 : Fin (p.tapeCount+12)) := by
        intro h;exact hv (congrArg Fin.val h)
      simp [b,nativePrefixReadState,Function.update_of_ne hbh,startState,hv,hb0])
    (by simp [b,nativePrefixReadState,Function.update_of_ne hbs,startState])
    (by intro i;fin_cases i <;> rfl) (by omega)
  refine ((WXExec.wm ec).seq ((WXExec.wm ef).seq ep)).mono ?_
  omega

end NearQuarticWires.StageCertificateControl
