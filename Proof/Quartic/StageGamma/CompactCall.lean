import Proof.Quartic.StageGamma.CompactBounds
import Proof.Quartic.StageGamma.RawAssembler
import Proof.Quartic.StageGamma.Response
import Proof.Gates.Cells.Lang

set_option autoImplicit false

namespace NearQuarticWires.StageGamma

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Interfaces
open NearCubicGates.Close.Expand.PolyTab

/-- `cor:conditional`, paper/paper.tex: the actual
nonblank Gaussian source, retaining the cached modulus and conjunction. -/
noncomputable def compactGaussInput (r : PreparedRequest) : List Bool :=
  rawInput (compactKernelInput r.1 r.2)

/-- `prop:time`, paper/paper.tex: all nonblank
source words together have linear serialized length in the actual seed. -/
theorem compactGaussInput_length_le (r : PreparedRequest) :
    (compactGaussInput r).length ≤ 6300 * (Cycle.seedLength r.1.parameters + 9) := by
  have hh := rawInput_length_le (compactKernelInput r.1 r.2)
    (100 * (Cycle.seedLength r.1.parameters + 9)) (compactKernelInput_length_le r.1 r.2)
  dsimp only [compactGaussInput]
  omega

/-- `cor:conditional`, paper/paper.tex: one fixed
machine loads the compact bank, performs actual Gaussian elimination and
returns both the consistency flag and unary nullity. -/
noncomputable def compactGaussProgram : WMX 32 1 :=
  .seq (rawProgram SeedFix.elimM) (.wm (appendGaussFlag (rawSlot 29) (rawSlot 30)))

/-- `prop:time`, paper/paper.tex: the complete
per-choice execution includes physical loading and output formation. -/
noncomputable def compactGaussCost (r : PreparedRequest) : ℕ :=
  rawCost (compactKernelInput r.1 r.2) (Machine.gammaGaussIterationCost r.1 r.2) +
    1 + (3 * kernelExponent r.1 r.2 + 6)

/-- `cor:conditional` and `prop:time`, paper/paper.tex: one genuine cold per-choice WordFunction consumes only
explicit nonblank input records and computes the exact Gaussian reply. -/
noncomputable def compactGaussWordFunction :
    WordFunction PreparedRequest compactGaussInput preparedResponse
      (fun r => 2 * compactGaussCost r + 2) :=
  wordFunction_of_ideal compactGaussProgram (rawSlot 30) (by decide)
    (fun r => rawCapacity (compactKernelInput r.1 r.2)) (fun _ _ => 0)
    compactGaussCost (fun _ => le_rfl) (by
      intro r
      obtain ⟨A, hk, hf, he⟩ := compactKernel_run r.1 r.2
      obtain ⟨τ, hr, hs, hh⟩ := raw_run SeedFix.elimM (compactKernelInput r.1 r.2)
        A (Machine.gammaGaussIterationCost r.1 r.2) hk
      have hscan := appendGaussFlag_run (rawCapacity (compactKernelInput r.1 r.2))
        (rawSlot 29) (rawSlot 30) (by decide) τ (kernelFlag r.1 r.2)
        (kernelExponent r.1 r.2) ((hs 29).trans hf) (hh 29) ((hs 30).trans he) (hh 30)
      let ρ := (τ.seth (rawSlot 30) (kernelExponent r.1 r.2 + 1)).sets (rawSlot 30)
        (preparedResponse r)
      refine ⟨rfl, ρ, ?_, ?_⟩
      · simpa only [idealStart, startState, List.replicate_zero, compactGaussInput,
          compactGaussProgram, compactGaussCost, ρ, preparedResponse] using
          WXExec.seq hr (WXExec.wm hscan)
      · simp only [ρ, WState.sets_st, Function.update_self])

/-- `prop:time`, paper/paper.tex: the actual complete
per-choice program has polynomial cost in S, with no primitive-field
search hidden in its repeated call budget. -/
theorem compactGaussCost_le (r : PreparedRequest) :
    2 * compactGaussCost r + 2 ≤ 1000000 * (Cycle.seedLength r.1.parameters + 9) ^ 6 := by
  have hi := compactGaussInput_length_le r
  have hk := Machine.gammaGaussIterationCost_le r.1 r.2
  have he : kernelExponent r.1 r.2 ≤ Cycle.seedLength r.1.parameters := by
    dsimp [kernelExponent, Cycle.seedLength]
    omega
  have hq : Cycle.seedLength r.1.parameters + 9 ≤ (Cycle.seedLength r.1.parameters + 9) ^ 6 := by
    calc
      _ = (Cycle.seedLength r.1.parameters + 9) ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)
  dsimp only [compactGaussCost, rawCost, compactGaussInput] at *
  nlinarith

/-- `cor:conditional`, paper/paper.tex: the enclosing
exact-radix source program calls this concrete Gaussian machine. -/
noncomputable def compactGaussCallee : NearCubicGates.Close.Cells.Callee :=
  ⟨PreparedRequest, compactGaussInput, preparedResponse,
    (fun r => 2 * compactGaussCost r + 2), compactGaussWordFunction⟩

end NearQuarticWires.StageGamma
