import Proof.Quartic.StageGamma.CompactCall

set_option autoImplicit false

namespace NearQuarticWires.StageGamma

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.RepairOrdinary.ZeroPadding (pad)
open NearCubicWires.WireExponent3_5

attribute [local irreducible] kernelCapacities

/-- `cor:conditional`, paper/paper.tex: the compact
Gaussian bank contains only constant-sized markers, actual numeric fields,
the cached modulus, the selected equations and a linear column counter. -/
def compactBank (ell plen pre modulus rest : ℕ) (cons : List Bool) : Fin 31 → List Bool :=
  ![List.replicate 8 true ++ [false], List.replicate ell true ++ [false],
    frame (binary ell 0), frame (binary ell 0), [], frame (binary ell modulus), [],
    frame (binary ell 0), frame (binary ell 0), [], [], [], [], [],
    frame (binary plen pre), frame (binary ell 0), [], [], [], [],
    frame (binary ell 1), [], cons, [], [], [], [], [],
    List.replicate rest true, [false], []]

/-- `cor:conditional`, paper/paper.tex: the finite
physical writer recipe is exactly the already verified Gaussian source. -/
theorem compactKernelInput_eq_bank (request : Machine.GammaRequest)
    (choice : Cycle.GammaChoice request.parameters.Q) :
    compactKernelInput request choice =
      compactBank request.parameters.ell request.prefixLength request.prefixCode
        request.parameters.modulus
        (Cycle.seedLength request.parameters - request.prefixLength)
        (SeedFix.consTape request.parameters.ell (2 * request.parameters.kh)
          (conjunction request choice) []) := by
  funext i
  fin_cases i <;>
    simp [compactKernelInput, blankKernelPort, compactBank, kernelInput,
      SeedFix.bank31, initialRegisters, pad, Cycle.seedLength]

end NearQuarticWires.StageGamma
