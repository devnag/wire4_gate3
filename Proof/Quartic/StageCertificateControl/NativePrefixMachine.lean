import Proof.Quartic.StageCertificateControl.NativePrefixExecution
import Proof.Gates.Expand.PolyTabPack

/-!
# Actual framed native-table prefixing with a linear total budget

Paper: `lem:print`, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Expand.PolyTab

/-- `prop:time`, paper/paper.tex: the
header wrapper pays its actual linear source clock and the final
parallel return of all physical heads. -/
def nativePrefixBudget (threshold inputLength budget : ℕ) : ℕ :=
  2*nativePrefixSourceSteps threshold inputLength budget+2

/-- `lem:print` and `prop:time`, paper/paper.tex: a fixed physical word function
prefixes the retained actual binary header to one actual native-table
computation, preserving its entire signed output byte for byte. -/
noncomputable def nativePrefixWordFunction {Request : Type} {input payload : Request→List Bool}
    {budget : Request→ℕ} (f : WordFunction Request input (fun r => frame (payload r)) budget)
    (threshold : Request→ℕ) :
    WordFunction Request (fun r => RepairRepresentation.natWord (threshold r)++input r)
      (fun r => frame (RepairRepresentation.natWord (threshold r)++payload r))
      (fun r => nativePrefixBudget (threshold r) (input r).length (budget r)) :=
  wordFunction_of_ideal (nativePrefixProgram f.program) (indexedFinal f.program) (by simp [indexedFinal])
    (fun r => nativePrefixSourceSteps (threshold r) (input r).length (budget r))
    (fun _ _ => 0) (fun r => nativePrefixSourceSteps (threshold r) (input r).length (budget r))
    (by intro r;exact Nat.le_refl _) (by intro r;exact ⟨rfl,nativePrefix_exec f r (threshold r)⟩)

/-- `prop:time`, paper/paper.tex: the
complete compiled wrapper has only one factor of the actual native
budget; no native census or runtime is squared. -/
theorem nativePrefixBudget_linear (threshold inputLength budget : ℕ) :
    nativePrefixBudget threshold inputLength budget≤
      20002*((RepairRepresentation.natWord threshold).length+inputLength+budget+1) := by
  unfold nativePrefixBudget nativePrefixSourceSteps
  omega

end NearQuarticWires.StageCertificateControl
