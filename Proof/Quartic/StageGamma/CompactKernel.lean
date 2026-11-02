import Proof.Quartic.StageGamma.Kernel
import Proof.Gates.CheckedPCPP.WMXReady

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageGamma

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.WireExponent3_5
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.RepairOrdinary.ZeroPadding (pad)
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.CheckedPCPP

attribute [local irreducible] kernelCapacities

/-- `cor:conditional`, paper/paper.tex: these input
ports contain only blank workspace cells, irrespective of the request. -/
def blankKernelPort (i : Fin 31) : Bool :=
  decide (i.val ∈ ([4, 6, 9, 10, 11, 12, 13, 16, 17, 18, 19, 21, 23, 24, 25, 26, 27] : List ℕ))

/-- `cor:conditional`, paper/paper.tex: the Gaussian
input with purely blank workspace tails represented by empty tapes. The
cached modulus, all marked numbers and the true column counter remain. -/
noncomputable def compactKernelInput (request : Machine.GammaRequest)
    (choice : Cycle.GammaChoice request.parameters.Q) (i : Fin 31) : List Bool :=
  if blankKernelPort i then [] else kernelInput request choice i

/-- `cor:conditional`, paper/paper.tex: every blank
workspace replacement preserves all physical tape reads. -/
theorem compactKernelInput_read (request : Machine.GammaRequest)
    (choice : Cycle.GammaChoice request.parameters.Q) (i : Fin 31) :
    RdEq (kernelInput request choice i) (compactKernelInput request choice i) := by
  unfold compactKernelInput
  split_ifs with hblank
  · apply rdEq_blank
    fin_cases i <;>
      simp_all [blankKernelPort, kernelInput, SeedFix.bank31, initialRegisters, pad]
  · exact RdEq.refl _

/-- `cor:conditional`, paper/paper.tex: replacing
blank workspace tails preserves the exact output tapes and execution
clock of the actual Gaussian machine. -/
theorem compactKernel_run (request : Machine.GammaRequest)
    (choice : Cycle.GammaChoice request.parameters.Q) :
    ∃ tapes : Fin 31 → List Bool,
      Step SeedFix.elimM (Machine.gammaGaussIterationCost request choice)
        (fun _ => 0) (compactKernelInput request choice) (fun _ => 0) tapes ∧
      tapes 29 = [kernelFlag request choice] ∧
      tapes 30 = List.replicate (kernelExponent request choice) true ++ [false] := by
  obtain ⟨tapes, ⟨r, hr, hh, ht, _⟩, hf, he⟩ := kernel_run_ports request choice
  let E : Fin 31 → Prop := fun i => i = 29 ∨ i = 30
  have hrel : ConfRel E
      (⟨SeedFix.elimM.start, fun _ => 0, kernelInput request choice⟩)
      (⟨SeedFix.elimM.start, fun _ => 0, compactKernelInput request choice⟩) := by
    refine ⟨rfl, rfl, compactKernelInput_read request choice, ?_⟩
    intro i hi
    rcases hi with rfl | rfl <;> rfl
  obtain ⟨r', hr', hrel', _⟩ := runFrom_rel SeedFix.elimM E
    (Machine.gammaGaussIterationCost request choice) hrel r hr
  refine ⟨r'.final.tapes, Step.of_run hr' ?_ rfl, ?_, ?_⟩
  · rw [← hrel'.heads, hh]
  · rw [← hrel'.exact 29 (by left; rfl), ht]
    exact hf
  · rw [← hrel'.exact 30 (by right; rfl), ht]
    exact he

end NearQuarticWires.StageGamma
