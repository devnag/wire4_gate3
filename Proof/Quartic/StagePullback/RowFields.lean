import Proof.Quartic.StagePullback.RowRequest
import Proof.Quartic.StageGamma.ReadFields

set_option autoImplicit false

namespace NearQuarticWires.StagePullback

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells

/-- `imp:pullback`, paper/paper.tex: retained scalar
variables of the original signed-row header, in its physical source order. -/
def rowFieldRegister : Fin 9 → Fin VV := ![20, NativeRows.fieldWidth, FieldOutput.width,
  21, 22, 23, 24, 27, 28]

/-- `imp:pullback`, paper/paper.tex: the actual
nine-field scalar request is decoded by fixed binary source control. -/
def rowFieldsProgram : St VV MM := StageGamma.readFields (List.ofFn rowFieldRegister)

/-- `imp:pullback` and `prop:time`, paper/paper.tex: the complete original signed-row header is physically
parsed, preserving the exact source cursor at its three raw flags. -/
theorem rowFields_parse (C : Ctx) (a : DS VV MM) (r : RowRequest)
    (hc : Cst a) (hip : a.ip = 0) (hinput : C.inp = r.word) (hwidth : r.Lout + 4 ≤ C.Wd) :
    Hs C rowFieldsProgram a (StageGamma.readFieldsCost r.fields) (fun b =>
      (∀ i : Fin 9, b.env (rowFieldRegister i) =
        r.fields[i.val]'(by rw [RowRequest.fields_length]; exact i.isLt)) ∧
      b.ip = (r.fields.flatMap natWord).length ∧
      (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.out, a.ram, a.rc, a.kin, a.kout, a.kc) ∧ Cst b ∧
      Fr a b (List.ofFn rowFieldRegister ++ vJ :: rdNatT)) := by
  have hs : ∀ x ∈ List.ofFn rowFieldRegister, x ∉ vJ :: rdNatT ∧ x ∉ [vZ, v1, v2] := by decide
  have hh := StageGamma.readFields_spec C (List.ofFn rowFieldRegister) (by decide) hs r.fields
    (by simp [RowRequest.fields_length]) a hc ([r.useLeft, r.useRight, r.transpose] ++ r.body)
    (by simp [hinput, hip, RowRequest.word, List.append_assoc]) (by
      intro v hv
      have := r.fields_bitLength v hv
      omega)
  refine Hs.mono hh le_rfl ?_
  rintro b ⟨hb, hbip, hrest, hbc, hfr⟩
  refine ⟨?_, by simpa only [hip, Nat.zero_add] using hbip, hrest, hbc, hfr⟩
  intro i
  simpa only [Fin.getElem_fin, List.getElem_ofFn] using
    hb ⟨i.val, by simpa only [List.length_ofFn] using i.isLt⟩

/-- `prop:time`, paper/paper.tex: the actual binary
row-header parser has a concrete linear clock in the signed output width. -/
theorem rowFields_cost (r : RowRequest) :
    StageGamma.readFieldsCost r.fields ≤ 270 * r.Lout + 568 := by
  have h := StageGamma.readFieldsCost_le r.fields (r.Lout + 1)
    (fun v hv => r.fields_bitLength v hv)
  rw [RowRequest.fields_length] at h
  omega

end NearQuarticWires.StagePullback
