import Proof.Quartic.StageGamma.Retain
import Proof.Quartic.StageGamma.FieldProducer

set_option autoImplicit false

namespace NearQuarticWires.StageGamma

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicGates.Close.Cells

/-- `cor:conditional`, paper/paper.tex: the second
stage reads the literal ORIGINAL request followed by the cached field bits. -/
def cachedRequestWord (request : Machine.GammaRequest) : List Bool :=
  Machine.gammaRequestWord request ++
    binary request.parameters.ell request.parameters.modulus

/-- `prop:time`, paper/paper.tex: the cold setup
budget includes physical copying of the ORIGINAL request and field cache. -/
noncomputable def cachedRequestBudget (request : Machine.GammaRequest) : ℕ :=
  2 * retainedCost (input := Machine.gammaRequestWord)
    (cache := fun r => binary r.parameters.ell r.parameters.modulus)
    (budget := fun r => 4 * fieldProducerCost r + 4 * unaryFieldCost r + 12) request + 2

/-- `cor:conditional` and `prop:time`, paper/paper.tex: a genuine cold ORIGINAL-codec producer performs exactly one
field setup and physically retains the entire request beside its cache. -/
noncomputable def cachedRequestWordFunction :
    WordFunction Machine.GammaRequest Machine.gammaRequestWord
      (fun request => frame (cachedRequestWord request)) cachedRequestBudget :=
  retainedWordFunction cachedFieldWordFunction

/-- `cor:conditional`, paper/paper.tex: the ORIGINAL
fourteen-field parser admits the actual physical field-cache suffix and
stops before it, preserving all decoded fields in their fixed variables. -/
theorem requestFields_parse_cached (C : Ctx) (request : Machine.GammaRequest)
    (hinput : C.inp = cachedRequestWord request)
    (hwidth : Cycle.seedLength request.parameters + 3 ≤ C.Wd)
    (a : DS VV MM) (hc : Cst a) (hip : a.ip = 0) :
    Hs C requestFieldsProgram a (readFieldsCost (requestFields request)) (fun b =>
      (∀ i : Fin 14, b.env (requestFieldRegister i) =
        (requestFields request)[i.val]'(by rw [requestFields_length]; exact i.isLt)) ∧
      b.ip = (Machine.gammaRequestWord request).length ∧
      (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.out, a.ram, a.rc, a.kin, a.kout, a.kc) ∧ Cst b) := by
  have hs : ∀ x ∈ List.ofFn requestFieldRegister, x ∉ vJ :: rdNatT ∧ x ∉ [vZ, v1, v2] := by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    simp only [rdNatT, List.mem_cons, List.not_mem_nil, or_false, not_or,
      requestFieldRegister, vJ, vZ, v1, v2, t0, t1, t2, t3, t4, Fin.mk.injEq]
    omega
  have hh := readFields_spec C (List.ofFn requestFieldRegister)
    (List.nodup_ofFn.mpr requestFieldRegister_injective) hs (requestFields request)
    (by simp [requestFields_length]) a hc
    (binary request.parameters.ell request.parameters.modulus)
    (by simp [hinput, hip, requestFields_word, cachedRequestWord]) (by
      intro v hv
      have := requestFields_bitLength request v hv
      omega)
  refine Hs.mono hh le_rfl ?_
  rintro b ⟨hb, hbip, hrest, hbc, _⟩
  refine ⟨?_, ?_, hrest, hbc⟩
  · intro i
    simpa only [Fin.getElem_fin, List.getElem_ofFn] using
      hb ⟨i.val, by simpa only [List.length_ofFn] using i.isLt⟩
  · simpa [hip, requestFields_word] using hbip

end NearQuarticWires.StageGamma
