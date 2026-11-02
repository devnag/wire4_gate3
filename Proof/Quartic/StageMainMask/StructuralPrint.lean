import Proof.Quartic.StageMainMask.StoredWord
import Proof.Quartic.StageMain.FinalRecord

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageMain.Controller StageLift StageMain.CallSkip

/-- `def:mask`, paper/paper.tex: the two actual
pattern codes are retained outside the binary printing registers. -/
def structuralLeft : Fin VV := 80
def structuralRight : Fin VV := 81

/-- `def:mask` and Step 4 of `sec:algorithm`, paper/paper.tex: the structural request has its selected cut,
block size, block count and two original pattern codes. -/
def structuralPrintFields : List FinalField :=
  [.parameter 13, .parameter 5, .parameter 3,
    .register structuralLeft, .register structuralRight]

/-- `def:mask`, paper/paper.tex: the exact five
metadata fields are printed after the retained original call. -/
def structuralPrint : St VV MM :=
  .seq (emitStoredWord callStore lengthCounter) (printFields structuralPrintFields)

/-- `def:mask` and `prop:time`, paper/paper.tex: the original call and all five metadata fields are physically
printed with their actual binary lengths and no incidence vector. -/
theorem structuralPrint_run (C : Ctx) (c : Call) (p : Cells.Parameters)
    (u v R : ℕ) (a : DS VV MM) (hc : Cst a) (hs : PrintSource c p a)
    (hlen : a.env lengthCounter = (callWord c).length)
    (hu : a.env structuralLeft = u) (hv : a.env structuralRight = v)
    (h64 : 64 ≤ C.Wd) (hR : R + 2 ≤ C.Wd)
    (hcall : (callWord c).length < 2 ^ C.Wd)
    (hbits : ∀ value ∈ [p.dstar, p.b, p.r, u, v], natBitLength value ≤ R) :
    Hs C structuralPrint a (20 * (callWord c).length + 400 * R + 3000) (fun b =>
      b.out = a.out ++ (callWord c ++ [p.dstar, p.b, p.r, u, v].flatMap natWord) ∧
      b.ip = a.ip ∧ b.ram = a.ram ∧ Cst b) := by
  have hsafe : ∀ x ∈ structuralPrintFields, x.Safe := by
    intro x hx
    simp only [structuralPrintFields, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> unfold FinalField.Safe <;> decide
  unfold structuralPrint
  refine (Hs.seq (t1 := 9 * (callWord c).length + 6)
    (t2 := 5 * (fieldPrintBound c R + 1) + 1)
    ((emitStoredWord_run C callStore lengthCounter (by decide) (callWord c) a hc hs.call
      hlen hcall).mono (by have := hs.callCursor; omega) (fun _ h => h)) ?_).mono
      (by unfold fieldPrintBound; omega) (fun _ h => h)
  rintro b ⟨hbout, hbip, _hbkin, hbram, hbrc, _hbkout, _hbkc, hbc, hbfr⟩
  have hbs : PrintSource c p b := ⟨hbram ▸ hs.call, hbram ▸ hs.parameters,
    by rw [hbrc, Function.update_self],
    by rw [hbrc, Function.update_of_ne (by decide : parameterStore ≠ callStore)]
       exact hs.parameterCursor⟩
  have hbu : b.env structuralLeft = u := (hbfr _ (by decide)).trans hu
  have hbv : b.env structuralRight = v := (hbfr _ (by decide)).trans hv
  have hvals : structuralPrintFields.map (fun x => x.value c p b) =
      [p.dstar, p.b, p.r, u, v] := by
    simp only [structuralPrintFields, List.map_cons, List.map_nil, FinalField.value,
      hbu, hbv]
    rfl
  have hprint := printFields_run C c p structuralPrintFields hsafe R b hbc hbs
    (by omega) (lt_trans (by omega) Nat.lt_two_pow_self) hR
    (lt_of_le_of_lt hR Nat.lt_two_pow_self) (by
      intro x hx
      apply hbits
      rw [← hvals]
      exact List.mem_map.mpr ⟨x, hx, rfl⟩)
  change Hs C (printFields structuralPrintFields) b
    (5 * (fieldPrintBound c R + 1) + 1) _ at hprint
  refine hprint.mono le_rfl ?_
  rintro d ⟨hdout, _hds, hdrest, hdc, _hdfr⟩
  have hdip : d.ip = b.ip := congrArg (fun t => t.1) hdrest
  have hdram : d.ram = b.ram := congrArg (fun t => t.2.1) hdrest
  refine ⟨?_, hdip.trans hbip, hdram.trans hbram, hdc⟩
  rw [hdout, hbout]
  have hflat : structuralPrintFields.flatMap (fun x => natWord (x.value c p b)) =
      [p.dstar, p.b, p.r, u, v].flatMap natWord := by
    rw [← hvals, List.flatMap_map]
  rw [hflat, List.append_assoc]

end NearQuarticWires.StageMainMask
