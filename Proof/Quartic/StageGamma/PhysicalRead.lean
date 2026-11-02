import Proof.Quartic.StageGamma.RequestFields
import Proof.Gates.Cells.Run

set_option autoImplicit false

namespace NearQuarticWires.StageGamma

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.Cells NearCubicGates.Close.WordPrograms

/-- `prop:time`, paper/paper.tex: explicitly reserved
physical capacity for a finite source-code block. -/
def sourceBlockCapacity (C : Ctx) (a : DS VV MM) (n : ℕ) : ℕ :=
  2 * C.Wd + 2 + (2 * C.inp.length + 2) + a.out.length + n +
    ((2 * C.Wd + 1) * ((∑ m : Fin MM, (a.ram m).length) + n + 1) + 1) + (Rk C + 2)

/-- `prop:time`, paper/paper.tex: every capacity
condition of the actual source compiler is met by the computed reserve. -/
theorem sourceBlockCapacity_ok (C : Ctx) (a : DS VV MM) (n : ℕ) (hW : 1 ≤ C.Wd) :
    CapOK C (sourceBlockCapacity C a n) a n := by
  refine ⟨hW, by dsimp [sourceBlockCapacity]; omega,
    by dsimp [sourceBlockCapacity]; omega, by dsimp [sourceBlockCapacity]; omega,
    ?_, by dsimp [sourceBlockCapacity]; omega⟩
  intro m
  have hsum : (a.ram m).length ≤ ∑ j : Fin MM, (a.ram j).length :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (a.ram j).length) (Finset.mem_univ m)
  have hh := Nat.mul_le_mul_left (2 * C.Wd + 1)
    (Nat.add_le_add_right (Nat.add_le_add_right hsum n) 1)
  dsimp [sourceBlockCapacity]
  omega

/-- `prop:time`, paper/paper.tex: the full fourteen-field
decoder has a concrete linear number of source-language operations. -/
theorem requestFieldsCost_le (request : Machine.GammaRequest) :
    readFieldsCost (requestFields request) ≤ 420 * Cycle.seedLength request.parameters + 883 := by
  have hh := readFieldsCost_le (requestFields request)
    (Cycle.seedLength request.parameters + 1) (requestFields_bitLength request)
  rw [requestFields_length] at hh
  omega

/-- `cor:conditional` and `prop:time`, paper/paper.tex: the ORIGINAL Gamma request is decoded by an actual compiled
multitape program, with all physical capacities discharged. -/
theorem requestFields_run (C : Ctx) (request : Machine.GammaRequest)
    (hinput : C.inp = Machine.gammaRequestWord request)
    (hwidth : Cycle.seedLength request.parameters + 3 ≤ C.Wd)
    (a : DS VV MM) (hc : Cst a) (hip : a.ip = 0) (ha : Valid C a)
    (σ : WState (NS MM (TS C) VV) (NR MM)) (hσ : Enc C a σ) :
    ∃ (b : DS VV MM) (τ : WState (NS MM (TS C) VV) (NR MM)),
      Enc C b τ ∧
      WXExec (sourceBlockCapacity C a (420 * Cycle.seedLength request.parameters + 883))
        (comp C.K requestFieldsProgram) σ τ
        ((420 * Cycle.seedLength request.parameters + 883) * KC C) ∧
      (∀ i : Fin 14, b.env (requestFieldRegister i) =
        (requestFields request)[i.val]'(by rw [requestFields_length]; exact i.isLt)) ∧
      b.ip = (Machine.gammaRequestWord request).length ∧ Cst b := by
  obtain ⟨b, n, hex, hn, hvals, hbip, _, hbc⟩ :=
    requestFields_parse C request hinput hwidth a hc hip
  have hcN := hn.trans (requestFieldsCost_le request)
  have hW : 1 ≤ C.Wd := by omega
  obtain ⟨τ, henc, hrun⟩ :=
    (comp_ok C (sourceBlockCapacity C a (420 * Cycle.seedLength request.parameters + 883))
      (callee_hB C) (Ex.mono hex hcN) ha σ hσ
      (sourceBlockCapacity_ok C a _ hW)).1
  exact ⟨b, τ, henc, hrun, hvals, hbip, hbc⟩

end NearQuarticWires.StageGamma
