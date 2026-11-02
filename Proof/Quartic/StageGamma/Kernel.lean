import Proof.Quartic.Machine.GammaWork
import Proof.Wire_3_5.SeedFixElim

set_option autoImplicit false

namespace NearQuarticWires.StageGamma

open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay)
open NearCubicWires.RepairOrdinary.ZeroPadding (pad)

/-- `cor:conditional`, paper/paper.tex: the actual conjunction
selected by one of the eight-digit radix choices. -/
noncomputable def conjunction (request : Machine.GammaRequest)
    (choice : Cycle.GammaChoice request.parameters.Q) : List (ℕ × ℕ) :=
  Cycle.gammaChoiceCons request.parameters request.walk choice

/-- `cor:conditional`, paper/paper.tex: fixed workspace lengths
for the row constructor and Gaussian conjunction count. -/
structure KernelCapacities where
  field : ℕ
  inner : ℕ
  table : ℕ
  rows : ℕ
  reset : ℕ

/-- `cor:conditional`, paper/paper.tex: all capacities are
computed from the actual request and conjunction length. -/
noncomputable def kernelCapacities (request : Machine.GammaRequest)
    (choice : Cycle.GammaChoice request.parameters.Q) : KernelCapacities :=
  let ell := request.parameters.ell
  let k := 2 * request.parameters.kh
  let plen := request.prefixLength
  let n := (conjunction request choice).length
  let rest := 8 * ell - plen
  ⟨2 * ell + 2 + (2 * rest + 13),
    ell * (SeedFix.innerCost ell + 2) + 1 +
      (ell * (GF2.mulIterCost ell + 2) + 1) +
      (plen * (SeedFix.phACost ell + 2) + 1) +
      (n * k * (Gauss.gaussCost 1 rest + 2) + 3) +
      (n * k * (Gauss.rowCost rest + 2) + 3) +
      (n * k * (2 * rest + 1) + 1),
    SeedFix.tableCost ell 8 + SeedFix.passesCost ell plen (8 * ell),
    k * (SeedFix.rowCost ell plen (8 * ell) + 2) + 1,
    SeedFix.loopCost ell 8 k plen n + 2 +
      Gauss.gaussCost (n * k) rest + SeedFix.Deficit.cost rest⟩

/-- `cor:conditional`, paper/paper.tex: blank initial
arithmetic registers with a correctly sized column-table workspace. -/
def initialRegisters (ell : ℕ) : SeedFix.Regs :=
  ⟨0, 0, 0, 0, 0, [], false, [], List.replicate (8 * (ell * (2 * ell + 1))) false⟩

/-- `cor:conditional`, paper/paper.tex: the row constructor's
register invariant holds for its explicit initial workspace. -/
theorem initialRegisters_ok (ell : ℕ) : (initialRegisters ell).Ok ell 8 := by
  simp [initialRegisters, SeedFix.Regs.Ok]

/-- `cor:conditional`, paper/paper.tex: the concrete 31-tape
input of one Gaussian kernel, including the cached modulus and every ruler. -/
noncomputable def kernelInput (request : Machine.GammaRequest)
    (choice : Cycle.GammaChoice request.parameters.Q) : Fin 31 → List Bool :=
  let P := request.parameters
  let C := kernelCapacities request choice
  let rest := 8 * P.ell - request.prefixLength
  SeedFix.bank31 P.modulus P.ell 8 request.prefixLength request.prefixCode
    1 C.field C.inner C.table C.rows (2 * P.ell + 1) (2 * P.ell + 1) C.reset
    (initialRegisters P.ell) []
    (SeedFix.consTape P.ell (2 * P.kh) (conjunction request choice) []) [] []
    (pad rest []) (pad rest (List.replicate rest true)) [false] []

/-- `cor:conditional`, paper/paper.tex: read the physical
consistency flag and unary nullity exponent as the exact solution count. -/
def kernelCount (tapes : Fin 31 → List Bool) : ℕ :=
  if (tapes 29).headD false then 2 ^ (tapes 30).count true else 0

/-- `cor:conditional`, paper/paper.tex: the Gaussian
consistency flag for the actual selected conjunction. -/
noncomputable def kernelFlag (request : Machine.GammaRequest)
    (choice : Cycle.GammaChoice request.parameters.Q) : Bool :=
  (JoinElimination.gauss (8 * request.parameters.ell - request.prefixLength)
    (JoinElimination.system request.parameters.modulus request.parameters.ell 8
      (2 * request.parameters.kh) request.prefixLength request.prefixCode
      (conjunction request choice))).1

/-- `cor:conditional`, paper/paper.tex: the nullity
of the actual conjunction's residual seed system. -/
noncomputable def kernelExponent (request : Machine.GammaRequest)
    (choice : Cycle.GammaChoice request.parameters.Q) : ℕ :=
  8 * request.parameters.ell - request.prefixLength -
    (JoinElimination.gauss (8 * request.parameters.ell - request.prefixLength)
      (JoinElimination.system request.parameters.modulus request.parameters.ell 8
        (2 * request.parameters.kh) request.prefixLength request.prefixCode
        (conjunction request choice))).2

/-- `cor:conditional`, paper/paper.tex: the actual finite
Gaussian machine computes each unpadded conjunction, with every workspace
condition discharged from the explicit input construction. -/
theorem kernel_run_ports (request : Machine.GammaRequest)
    (choice : Cycle.GammaChoice request.parameters.Q) :
    ∃ tapes : Fin 31 → List Bool,
      Step SeedFix.elimM (Machine.gammaGaussIterationCost request choice)
        (fun _ => 0) (kernelInput request choice) (fun _ => 0) tapes ∧
      tapes 29 = [kernelFlag request choice] ∧
      tapes 30 = List.replicate (kernelExponent request choice) true ++ [false] := by
  let P := request.parameters
  let cs := conjunction request choice
  let C := kernelCapacities request choice
  let rest := 8 * P.ell - request.prefixLength
  have hplen : request.prefixLength ≤ 8 * P.ell := request.prefixFits
  have hcons : ∀ con ∈ cs, con.1 < 2 ^ P.ell := by
    intro con hcon
    exact (Cycle.gammaChoiceCons_bounds P request.walk choice con hcon).1
  have hp := SeedFix.elim_ports P.modulus P.ell 8 (2 * P.kh)
    request.prefixLength request.prefixCode 1 C.field C.inner C.table C.rows
    (2 * P.ell + 1) (2 * P.ell + 1) C.reset rest rest
    (initialRegisters P.ell) cs [] [] [] [] [] false
    P.cert.2.1 P.one_le_ell P.k_le (initialRegisters_ok P.ell) hcons
    (by dsimp [C, kernelCapacities, P]; omega)
    (by dsimp [C, kernelCapacities, P]; omega)
    (by dsimp [C, kernelCapacities, P]; omega)
    (by dsimp [C, kernelCapacities, P]; omega)
    (by dsimp [C, kernelCapacities, P]; omega)
    (by dsimp [C, kernelCapacities, P]; omega)
    (by dsimp [C, kernelCapacities, P]; omega)
    hplen (by omega) (by omega) (by omega)
    (by dsimp [C, kernelCapacities, rest, P]; omega)
    (by dsimp [C, kernelCapacities, cs, P]; omega)
    (by dsimp [C, kernelCapacities, cs, P]; omega)
    (by omega)
    (by dsimp [C, kernelCapacities, cs, P]; omega)
    (by dsimp [C, kernelCapacities, cs, rest, P]; omega)
    (by dsimp [C, kernelCapacities, rest, P]; omega)
  obtain ⟨tapes, hrun, hflag, hexponent, _, _⟩ := hp
  exact ⟨tapes, hrun, hflag, by simpa [overlay, kernelExponent, P, cs] using hexponent⟩

/-- `cor:conditional`, paper/paper.tex: the physical
flag and unary nullity determine precisely the requested completion count. -/
theorem kernel_run (request : Machine.GammaRequest)
    (choice : Cycle.GammaChoice request.parameters.Q) :
    ∃ tapes : Fin 31 → List Bool,
      Step SeedFix.elimM (Machine.gammaGaussIterationCost request choice)
        (fun _ => 0) (kernelInput request choice) (fun _ => 0) tapes ∧
      kernelCount tapes =
        (JoinElimination.condProbGauss request.parameters.modulus request.parameters.ell 8
          (2 * request.parameters.kh) request.prefixLength request.prefixCode
          (conjunction request choice)).1 := by
  obtain ⟨tapes, hrun, hflag, hexponent⟩ := kernel_run_ports request choice
  refine ⟨tapes, hrun, ?_⟩
  simpa [kernelCount, hflag, hexponent, kernelFlag, kernelExponent] using
    SeedFix.elim_count request.parameters.modulus request.parameters.ell 8
      (2 * request.parameters.kh) request.prefixLength request.prefixCode (conjunction request choice)

/-- `prop:time`, paper/paper.tex: the realized Gaussian
kernel has the proved polynomial cost on each of the exact `(Q+1)^8` choices. -/
theorem kernel_run_bounded (request : Machine.GammaRequest)
    (choice : Cycle.GammaChoice request.parameters.Q) :
    ∃ tapes : Fin 31 → List Bool,
      Step SeedFix.elimM (3000 * (Cycle.seedLength request.parameters + 9) ^ 6)
        (fun _ => 0) (kernelInput request choice) (fun _ => 0) tapes ∧
      kernelCount tapes =
        (JoinElimination.condProbGauss request.parameters.modulus request.parameters.ell 8
          (2 * request.parameters.kh) request.prefixLength request.prefixCode
          (conjunction request choice)).1 := by
  obtain ⟨tapes, hrun, hout⟩ := kernel_run request choice
  exact ⟨tapes, hrun.enlarge (Machine.gammaGaussIterationCost_le request choice), hout⟩

end NearQuarticWires.StageGamma
