import Proof.Quartic.StageGamma.WriterBudget

set_option autoImplicit false

namespace NearQuarticWires.StageGamma

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open NearCubicGates.Close.CounterMachine.CellTablesProg
open NearCubicWires.WireExponent3_5

/-- `cor:conditional`, paper/paper.tex: the binary
registers needed by one actual Gaussian call, all tied to the ORIGINAL
request, its true radix choice and the once-computed primitive modulus. -/
structure BankReady (request : Machine.GammaRequest)
    (choice : Cycle.GammaChoice request.parameters.Q) (a : DS VV MM) : Prop where
  ell : a.env (requestFieldRegister 0) = request.parameters.ell
  plen : a.env (requestFieldRegister 3) = request.prefixLength
  pre : a.env (requestFieldRegister 4) = request.prefixCode
  modulus : a.env gammaModulus = request.parameters.modulus
  rest : a.env gammaRest = Cycle.seedLength request.parameters - request.prefixLength
  cellWidth : a.env gammaCellWidth = 2 * request.parameters.kh
  digit : ∀ slot, a.env (gammaDigit slot) = (choice slot).val
  label : ∀ slot, a.env (gammaLabel slot) = (choice slot).val - 1
  cell : ∀ slot, a.env (gammaCell slot) =
    Sampler.cellNum request.parameters (Cycle.edge (by norm_num) request.walk slot)

/-- `cor:conditional`, paper/paper.tex: the complete
producer prints exactly the concrete compact Gaussian callee input. -/
theorem gammaBankWriter_bits (request : Machine.GammaRequest)
    (choice : Cycle.GammaChoice request.parameters.Q) (a : DS VV MM)
    (hc : Cst a) (ha : BankReady request choice a) :
    gammaBankWriter.bits a = compactGaussInput ⟨request, choice⟩ := by
  rw [gammaBankWriter, bankRecipe_bits consRecipe a request.parameters.ell request.prefixLength
    request.prefixCode request.parameters.modulus
    (Cycle.seedLength request.parameters - request.prefixLength) hc
    ha.ell ha.plen ha.pre ha.modulus ha.rest,
    consRecipe_bits request choice a ha.ell ha.cellWidth ha.digit ha.label ha.cell]
  dsimp only [compactGaussInput]
  rw [compactKernelInput_eq_bank]

/-- `cor:conditional`, paper/paper.tex: repeated
calls reserve only the concrete compact Gaussian kernel, never field search. -/
noncomputable def gaussContext (width : ℕ) (input : List Bool) (L B : ℕ) : Ctx :=
  ⟨width, input, compactGaussCallee, L, B⟩

/-- `cor:conditional`, paper/paper.tex: a single
fixed control physically writes every kernel input bit and invokes the
already closed ordinary Gaussian program. -/
def gammaGaussCall : St VV MM :=
  .seq gammaBankWriter.program (.op .kcall)

/-- `cor:conditional` and `prop:time`, paper/paper.tex: one actual source call computes the exact consistency and
nullity response, preserving all ORIGINAL fields outside writer scratch. -/
theorem gammaGaussCall_run (request : Machine.GammaRequest)
    (choice : Cycle.GammaChoice request.parameters.Q) (width : ℕ) (input : List Bool)
    (L B : ℕ) (a : DS VV MM) (hc : Cst a) (hW : 2 ≤ width)
    (ha : BankReady request choice a) (hkin : a.kin = [])
    (hfit : ∀ x ∈ gammaBankWriter.params, a.env x < 2 ^ width)
    (hroom : gammaBankWriter.cost a ≤ L)
    (hbudget : 2 * compactGaussCost ⟨request, choice⟩ + 2 ≤ B) :
    Hs (gaussContext width input L B) gammaGaussCall a
      (gammaBankWriter.cost a + (1 + L + B) + 1) (fun b =>
        b.kout = preparedResponse ⟨request, choice⟩ ∧ b.kc = 0 ∧ b.kin = [] ∧
        b.ip = a.ip ∧ b.out = a.out ∧ b.ram = a.ram ∧ b.rc = a.rc ∧
        Cst b ∧ Fr a b writerScratch) := by
  let C := gaussContext width input L B
  have hw : Hs C gammaBankWriter.program a (gammaBankWriter.cost a) (fun b =>
      b.kin = a.kin ++ gammaBankWriter.bits a ∧ SameN a b ∧ Cst b ∧
      Fr a b writerScratch) :=
    gammaBankWriter.run gammaBankWriter_safe C a hc hW hfit
      (by simpa [C, gaussContext, hkin] using hroom)
  refine Hs.seq (t1 := gammaBankWriter.cost a) (t2 := 1 + L + B) hw ?_
  intro b ⟨hb, hs, hbc, hfr⟩
  have hin : b.kin = C.K.inw ⟨request, choice⟩ := by
    simpa [C, gaussContext, compactGaussCallee, hkin, gammaBankWriter_bits request choice a hc ha]
      using hb
  have he : Hs C (.op .kcall) b (1 + L + B)
      (fun d => d = b.called (preparedResponse ⟨request, choice⟩)) :=
    Hs.op (OpEx.kcall (C := C) (⟨request, choice⟩ : PreparedRequest) b hin hbudget) rfl
  refine Hs.mono he le_rfl ?_
  rintro d rfl
  exact ⟨rfl, rfl, rfl, hs.ip, hs.out, hs.ram, hs.rc,
    ⟨hbc.z, hbc.one, hbc.two⟩, hfr⟩

end NearQuarticWires.StageGamma
