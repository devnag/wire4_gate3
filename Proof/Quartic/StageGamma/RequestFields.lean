import Proof.Quartic.StageGamma.ReadFields
import Proof.Quartic.StageGamma.IntegerBounds

set_option autoImplicit false

namespace NearQuarticWires.StageGamma

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces
open NearCubicGates.Close.CounterMachine.CellTablesProg

/-- `cor:conditional`, paper/paper.tex: the complete
original coefficient request has fourteen explicitly encoded naturals. -/
def requestFields (request : Machine.GammaRequest) : List ℕ :=
  [request.parameters.ell, request.parameters.kh, request.parameters.Q,
    request.prefixLength, request.prefixCode, 8] ++
      List.ofFn (fun slot => (request.walk slot).val)

/-- `cor:conditional`, paper/paper.tex: the source
field count is fixed independently of every request value. -/
theorem requestFields_length (request : Machine.GammaRequest) :
    (requestFields request).length = 14 := by simp [requestFields]

/-- `cor:conditional`, paper/paper.tex: the field
parser consumes exactly the ORIGINAL Gamma request encoding. -/
theorem requestFields_word (request : Machine.GammaRequest) :
    (requestFields request).flatMap natWord = Machine.gammaRequestWord request := by
  simp [requestFields, Machine.gammaRequestWord, listWord]

/-- `cor:conditional`, paper/paper.tex: every original
numeric input fits within one more than the seed length's binary width. -/
theorem requestFields_lt (request : Machine.GammaRequest) (v : ℕ)
    (hv : v ∈ requestFields request) :
    v < 2 ^ (Cycle.seedLength request.parameters + 1) := by
  let S := Cycle.seedLength request.parameters
  have hell : request.parameters.ell ≤ S := by dsimp [S, Cycle.seedLength]; omega
  have hkh : request.parameters.kh ≤ S := by
    have := request.parameters.k_le
    omega
  have h8 : 8 ≤ S := by
    have := request.parameters.one_le_ell
    dsimp [S, Cycle.seedLength]
    omega
  have hS : S < 2 ^ (S + 1) := by
    have h : S < 2 ^ S := Nat.lt_two_pow_self
    have hp := Nat.pow_le_pow_right (n := 2) (by decide) (show S ≤ S + 1 by omega)
    omega
  have hpow : 2 ^ S < 2 ^ (S + 1) := Nat.pow_lt_pow_right (by decide) (by omega)
  have hQ : request.parameters.Q < 2 ^ (S + 1) :=
    lt_of_le_of_lt (request.parameters.Q_le.trans
      (Nat.pow_le_pow_right (by decide) hell)) hpow
  have hpre : request.prefixCode < 2 ^ (S + 1) :=
    (request.prefixCodeFits.trans_le (Nat.pow_le_pow_right (by decide) request.prefixFits)).trans hpow
  simp only [requestFields, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_ofFn] at hv
  rcases hv with (rfl | rfl | rfl | rfl | rfl | rfl) | ⟨i, rfl⟩
  · exact lt_of_le_of_lt hell hS
  · exact lt_of_le_of_lt hkh hS
  · exact hQ
  · exact lt_of_le_of_lt request.prefixFits hS
  · exact hpre
  · exact lt_of_le_of_lt h8 hS
  · exact ((request.walk i).isLt.trans_le
      (Nat.pow_le_pow_right (by decide) hkh)).trans hpow

/-- `prop:time`, paper/paper.tex: the real request's
numeric fields have uniformly bounded binary length, including arbitrary
prefix bits and all eight original walk vertices. -/
theorem requestFields_bitLength (request : Machine.GammaRequest) (v : ℕ)
    (hv : v ∈ requestFields request) :
    natBitLength v ≤ Cycle.seedLength request.parameters + 1 :=
  natBitLength_le_of_lt v (Cycle.seedLength request.parameters + 1) (by omega)
    (requestFields_lt request v hv)

/-- `cor:conditional`, paper/paper.tex: fourteen fixed
binary variables retain the complete original request. -/
def requestFieldRegister (i : Fin 14) : Fin VV := ⟨20 + i.val, by change 20 + i.val < 128; omega⟩

/-- `cor:conditional`, paper/paper.tex: distinct source
fields occupy distinct variables. -/
theorem requestFieldRegister_injective : Function.Injective requestFieldRegister := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  dsimp [requestFieldRegister] at this
  omega

/-- `cor:conditional`, paper/paper.tex: fixed parser
control for the actual fourteen-field request word. -/
def requestFieldsProgram : St VV MM :=
  readFields (List.ofFn requestFieldRegister)

/-- `cor:conditional`, paper/paper.tex: every original
Gamma field is decoded with the exact cursor and no additional input. -/
theorem requestFields_parse (C : Ctx) (request : Machine.GammaRequest)
    (hinput : C.inp = Machine.gammaRequestWord request)
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
    (by simp [requestFields_length]) a hc []
    (by simp [hinput, hip, requestFields_word]) (by
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
