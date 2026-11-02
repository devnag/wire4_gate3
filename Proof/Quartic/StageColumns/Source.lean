import Proof.Quartic.StageColumns.Metadata
import Proof.Quartic.StageGamma.ReadFields

set_option autoImplicit false

namespace NearQuarticWires.StageColumns

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.Cells

/-- `prop:time`, paper/paper.tex: every field has
binary length bounded by the original input dimension. -/
theorem field_bitLength (P : StarParams) (v : ℕ) (hv : v ∈ fields P) :
    natBitLength v ≤ P.n + 1 := by
  have h := Nat.log_le_self 2 v
  have hvn := fields_le P v hv
  unfold natBitLength
  omega

def sourceRegisters : List (Fin VV) := [20, 21, 22, 23]

def sourceProgram : St VV MM := .seq (StageGamma.readFields sourceRegisters) metadataProgram

/-- `imp:partition`, `lem:print` and `prop:time`, paper/paper.tex: physically parse the four
original fields and derive every retained column dimension. -/
theorem sourceProgram_run (C : Ctx) (a : DS VV MM) (P : StarParams)
    (hc : Cst a) (hip : a.ip = 0) (hinput : C.inp = columnInput P)
    (hwidth : P.n + 4 ≤ C.Wd) :
    Hs C sourceProgram a (400 * (P.n + 2)) (fun b =>
      Prepared b P ∧ b.ip = (columnInput P).length ∧
      (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.out, a.ram, a.rc, a.kin, a.kout, a.kc)) := by
  have hcost := StageGamma.readFieldsCost_le (fields P) (P.n + 1)
    (fun v hv => field_bitLength P v hv)
  have hlen : (fields P).length = 4 := rfl
  rw [hlen] at hcost
  unfold sourceProgram
  refine Hx.hs (Hs.then (StageGamma.readFields_spec C sourceRegisters
    (by decide) (by decide) (fields P) rfl a hc []
    (by rw [hip, List.drop_zero, hinput, fields_word, List.append_nil])
    (fun v hv => by have h := field_bitLength P v hv; omega))
    (fun b ⟨hfields, hbip, hbrest, hbc, _⟩ n1 hn1 => ?_))
  have h20 : b.env 20 = P.n := by simpa [sourceRegisters, fields] using hfields ⟨0, by decide⟩
  have h21 : b.env 21 = P.r := by simpa [sourceRegisters, fields] using hfields ⟨1, by decide⟩
  have h22 : b.env 22 = P.b := by simpa [sourceRegisters, fields] using hfields ⟨2, by decide⟩
  have h23 : b.env 23 = P.s := by simpa [sourceRegisters, fields] using hfields ⟨3, by decide⟩
  refine Hs.last (metadataProgram_run C b P hbc h20 h21 h22 h23 hwidth) ?_
  rintro c ⟨hp, hcsh, _⟩ n2 hn2
  have hs := Same.of_sh hcsh
  refine ⟨⟨hp, ?_, ?_⟩, by omega⟩
  · rw [hs.ip, hbip, hip, fields_word, Nat.zero_add]
  · rw [hs.out, hs.ram, hs.rc, hs.kin, hs.kout, hs.kc]
    exact hbrest

end NearQuarticWires.StageColumns
