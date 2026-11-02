import Proof.Quartic.StageGamma.UnaryOutput
import Proof.Quartic.StageGamma.UnaryField
import Proof.Quartic.StageGamma.PhysicalRead
import Proof.Quartic.Program.Pipe
import Proof.Gates.Cells.Prelude
import Proof.Gates.CounterMachine.PrefixRun

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageGamma

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.Interfaces

/-- `imp:seed`, paper/paper.tex: the degree producer
makes no subroutine call. -/
noncomputable def fieldProducerCallee : Callee :=
  ⟨Empty, fun e => e.elim, fun e => e.elim, fun e => e.elim,
    wordFunction_of_wmx (WMX.skip : WMX 1 0) 1 (by decide) (fun _ => 0) (fun e => e.elim)⟩

/-- `prop:time`, paper/paper.tex: binary parser
workspace is polynomial in the degree encoded in the first source word. -/
def fieldProducerSizes : Sz := ⟨64, 1, 0, 0, 0, 0⟩

/-- `imp:seed`, paper/paper.tex: the actual original
Gamma header determines the producer's binary workspace width. -/
theorem fieldProducerWidth (request : Machine.GammaRequest) :
    Cycle.seedLength request.parameters + 3 ≤
      fieldProducerSizes.W (leadOnes (Machine.gammaRequestWord request)) := by
  have hl : leadOnes (Machine.gammaRequestWord request) = natBitLength request.parameters.ell := by
    unfold Machine.gammaRequestWord
    simp only [List.append_assoc]
    exact NearCubicGates.Close.CounterMachine.PrefixProg.leadOnes_natWord _ _
  have hp := lt_natBitLength request.parameters.ell
  simp only [fieldProducerSizes, Sz.W, one_mul, hl]
  dsimp [Cycle.seedLength]
  omega

/-- `imp:seed`, paper/paper.tex: fixed control decodes
the original request and writes the unary degree used for cached setup. -/
def fieldProducerProgram : St VV MM :=
  .seq initP (.seq requestFieldsProgram (unaryOutput (requestFieldRegister 0)))

/-- `imp:seed` and `prop:time`, paper/paper.tex: the ORIGINAL Gamma request physically produces the unary setup
input in a linear number of source-language operations. -/
theorem fieldProducer_run (C : Ctx) (request : Machine.GammaRequest)
    (hinput : C.inp = Machine.gammaRequestWord request)
    (hwidth : Cycle.seedLength request.parameters + 3 ≤ C.Wd) :
    Hs C fieldProducerProgram (a0 : DS VV MM)
      (500 * (Cycle.seedLength request.parameters + 9))
      (fun b => b.out = frame (unaryFieldInput request)) := by
  have hell : request.parameters.ell ≤ Cycle.seedLength request.parameters := by
    dsimp [Cycle.seedLength]
    omega
  have h4 : 4 ≤ 2 ^ C.Wd := by
    have htwo : 2 ≤ C.Wd := by omega
    exact Nat.pow_le_pow_right (n := 2) (by decide) htwo
  unfold fieldProducerProgram
  refine Hs.mono (Hs.seq (t2 := (420 * Cycle.seedLength request.parameters + 883) +
      (7 * request.parameters.ell + 6) + 1)
    (initP_spec (C := C) (a0 : DS VV MM) rfl rfl rfl (by omega))
    (fun a1 ⟨hc, _, _, hip, hout, _, _, _, _⟩ => ?_)) (by omega) (fun _ h => h)
  have hp := Hs.mono (requestFields_parse C request hinput hwidth a1 hc hip)
    (requestFieldsCost_le request) (fun _ h => h)
  refine Hs.seq (t1 := 420 * Cycle.seedLength request.parameters + 883)
    (t2 := 7 * request.parameters.ell + 6) hp (fun b ⟨hb, _, hrest, _⟩ => ?_)
  have hdeg : b.env (requestFieldRegister 0) = request.parameters.ell := by
    simpa [requestFields] using hb 0
  have hfit : request.parameters.ell < 2 ^ C.Wd := by
    have h : Cycle.seedLength request.parameters < 2 ^ Cycle.seedLength request.parameters :=
      Nat.lt_two_pow_self
    exact (lt_of_le_of_lt hell h).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have hup := unaryOutput_spec C (requestFieldRegister 0) (by decide) b request.parameters.ell hdeg hfit
  refine Hs.mono hup le_rfl ?_
  rintro e ⟨he, _, _⟩
  have hbout : b.out = a1.out := congrArg Prod.fst hrest
  rw [he, hbout, hout]
  rfl

/-- `prop:time`, paper/paper.tex: the producer's
native physical clock includes setup, compilation and final head reset. -/
noncomputable def fieldProducerCost (request : Machine.GammaRequest) : ℕ :=
  langBudget fieldProducerCallee fieldProducerSizes VV MM (Machine.gammaRequestWord request)
    (500 * (Cycle.seedLength request.parameters + 9))

/-- `imp:seed`, paper/paper.tex: a genuine cold
WordFunction produces the degree source from the ORIGINAL Gamma codec. -/
noncomputable def fieldProducerWordFunction :
    WordFunction Machine.GammaRequest Machine.gammaRequestWord
      (fun request => frame (unaryFieldInput request)) fieldProducerCost :=
  wordFunction_of_lang Machine.gammaRequestWord (fun request => frame (unaryFieldInput request))
    fieldProducerCallee fieldProducerSizes fieldProducerProgram
    (fun request => 500 * (Cycle.seedLength request.parameters + 9)) (by
      intro request
      obtain ⟨b, n, hex, hn, hout⟩ := fieldProducer_run
        (ctxOf fieldProducerCallee fieldProducerSizes (Machine.gammaRequestWord request)) request rfl
        (fieldProducerWidth request)
      exact ⟨b, n, hex, hout, hn⟩) (by
      intro request
      have h := fieldProducerWidth request
      omega)

/-- `imp:seed`, paper/paper.tex: the complete cached
field setup starts from the ORIGINAL Gamma request and invokes the actual
primitive search exactly once after physically producing its degree input. -/
noncomputable def cachedFieldWordFunction :
    WordFunction Machine.GammaRequest Machine.gammaRequestWord
      (fun request => frame (NearCubicWires.RepairOrdinary.SignedSortKey.binary
        request.parameters.ell request.parameters.modulus))
      (fun request => 4 * fieldProducerCost request + 4 * unaryFieldCost request + 12) :=
  NearQuarticWires.Program.WordFunction.pipe fieldProducerWordFunction unaryFieldWordFunction

end NearQuarticWires.StageGamma
