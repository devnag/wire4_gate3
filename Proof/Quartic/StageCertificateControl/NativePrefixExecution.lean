import Proof.Quartic.StageCertificateControl.NativePrefixCall
import Proof.Quartic.StageCertificateControl.NativePrefixEmit
import Proof.Quartic.StageCertificateControl.NativePrefixAvoid

/-!
# Complete physical threshold prefixing around a whole native table

Paper: `eq:testX`–`eq:testPhi`, paper/paper.tex,
`lem:print`, and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close NearCubicGates.Close.Interfaces NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.CheckedPCPP
open NearQuarticWires.Control

/-- `prop:time`, paper/paper.tex: a linear
scale in genuine encoded input bytes and the actual native computation
budget pays the complete header-retaining source execution. -/
def nativePrefixSourceSteps (threshold inputLength budget : ℕ) : ℕ :=
  10000*((RepairRepresentation.natWord threshold).length+inputLength+budget+1)

/-- `eq:testX`–`eq:testPhi`, `lem:print`, and `prop:time`,
paper/paper.tex:
the actual cold wrapper copies the binary threshold without decoding
its numeric value, invokes the given actual whole native word function
on the literal base input, and prefixes its unchanged output. Every
copy, machine call, bank erase and measured tape return is included
within a source clock linear in the actual native budget. -/
theorem nativePrefix_exec {Request : Type} {input payload : Request→List Bool} {budget : Request→ℕ}
    (f : WordFunction Request input (fun r => frame (payload r)) budget) (r : Request) (threshold : ℕ) :
    let p := f.program
    let cap := nativePrefixSourceSteps threshold (input r).length (budget r)
    ∃ τ, WXExec cap (nativePrefixProgram p)
      (startState (p.tapeCount+11) 32 (RepairRepresentation.natWord threshold++input r)) τ cap ∧
      τ.st (indexedFinal p)=frame (RepairRepresentation.natWord threshold++payload r) := by
  let p := f.program
  let cap := nativePrefixSourceSteps threshold (input r).length (budget r)
  have hout := Control.output_length_le f r
  have hframe : (frame (payload r)).length=2*(payload r).length+1 := by simp [Codec.frame_eq_marks]
  have hload : 100*((RepairRepresentation.natWord threshold).length+(input r).length+1)≤cap := by
    dsimp [cap,nativePrefixSourceSteps]
    omega
  have hcall : 2*(input r).length+2+budget r≤cap := by dsimp [cap,nativePrefixSourceSteps];omega
  have hcopy : (frame (payload r)).length+1≤cap := by dsimp [cap,nativePrefixSourceSteps];omega
  have hemit : 100*((RepairRepresentation.natWord threshold).length+(payload r).length+1)≤cap := by
    rw [hframe] at hout
    dsimp [cap,nativePrefixSourceSteps]
    omega
  have hcost : 1000*((RepairRepresentation.natWord threshold).length+(input r).length+1)+1+
      (nativePrefixCallCost (input r).length (budget r) (payload r)+1+
        100*((RepairRepresentation.natWord threshold).length+(payload r).length+1))≤cap := by
    rw [hframe] at hout
    dsimp [cap,nativePrefixSourceSteps,nativePrefixCallCost,StagePrint.callAppendCost]
    rw [hframe]
    omega
  have el := nativePrefixLoad_exec p threshold cap (input r) hload
  obtain ⟨τcall,ec,hs⟩ := nativePrefixCall_exec f r threshold cap hcall hcopy
  have ha := nativePrefixPrior_avoids_final p
  have hlf := NearQuarticWires.Control.WXExec.avoids el ha.1
  have hcf := NearQuarticWires.Control.WXExec.avoids ec ha.2
  have ho : τcall.st (indexedFinal p)=[] := by
    rw [hcf.1,hlf.1]
    simp [startState,indexedFinal]
  have hoh : τcall.sh (indexedFinal p)=0 := by rw [hcf.2,hlf.2];rfl
  have hf := nativePrefixReady_frames p threshold (input r) (payload r)
  have hH : ∀ q,readTapeBit (τcall.st (indexedExternal p 1))
      (τcall.sh (indexedExternal p 1)+q)=readTapeBit (frame (RepairRepresentation.natWord threshold)) q := by
    intro q
    rw [hs.sh]
    refine (hs.st _ _).symm.trans ?_
    rw [hf.1,hf.2.1,Nat.zero_add]
  have hB : ∀ q,readTapeBit (τcall.st (indexedExternal p 2))
      (τcall.sh (indexedExternal p 2)+q)=readTapeBit (frame (payload r)) q := by
    intro q
    rw [hs.sh]
    refine (hs.st _ _).symm.trans ?_
    rw [hf.2.2.1,hf.2.2.2.1,Nat.zero_add]
  obtain ⟨τ,ee,hresult⟩ := nativePrefixEmit_exec p cap (RepairRepresentation.natWord threshold) (payload r) τcall
    hH hB ho hoh (by rw [hs.val];exact hf.2.2.2.2.1) (by rw [hs.val];exact hf.2.2.2.2.2) hemit
  exact ⟨τ,(el.seq (ec.seq ee)).mono hcost,hresult⟩

end NearQuarticWires.StageCertificateControl
