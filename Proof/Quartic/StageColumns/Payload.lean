import Proof.Quartic.StageColumns.Columns
import Proof.Quartic.StageRecovery.NaturalPrint

set_option autoImplicit false

namespace NearQuarticWires.StageColumns

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.Cells

def payloadProgram : St VV MM :=
  .seq (StageRecovery.emitVariable nativeWidth) columnsProgram

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual width header precedes the exact canonical
column stream, with all physical output instructions charged. -/
theorem payloadProgram_run (C : Ctx) (a : DS VV MM) (P : StarParams)
    (h : Prepared a P) (hwidth : P.n + 4 ≤ C.Wd) :
    Hs C payloadProgram a (40 * (P.n + 1) + 43 + columnsClock P) (fun b =>
      b.out = a.out ++ (natWord (PrimT.C4Geo.width P) ++ columnStream P)) := by
  have hWn := (dimensions_le P).1
  have hsmall := StageHamming.scalar_word_bound P C.Wd hwidth
  have hbits : natBitLength (PrimT.C4Geo.width P) ≤ P.n + 1 := by
    unfold natBitLength
    have hlog := Nat.log_le_self 2 (PrimT.C4Geo.width P)
    omega
  have hem := StageRecovery.emitVariable_spec C a h.constants nativeWidth
    (by decide) (by omega) (by rw [h.width]; omega)
  rw [h.width] at hem
  unfold payloadProgram
  refine (Hs.seq (t2 := columnsClock P) hem (fun b ⟨hout, _, hbc, hf⟩ => ?_)).mono (by omega) (fun _ hs => hs)
  have hp : Prepared b P := ⟨hbc,
    (hf _ (by decide)).trans h.blockWidth, (hf _ (by decide)).trans h.parityWidth,
    (hf _ (by decide)).trans h.width, (hf _ (by decide)).trans h.dimension,
    (hf _ (by decide)).trans h.left, (hf _ (by decide)).trans h.data,
    (hf _ (by decide)).trans h.count⟩
  refine (columnsProgram_run C b P hp hwidth).mono le_rfl ?_
  rintro d ⟨hdo, _, _⟩
  rw [hdo, hout, List.append_assoc]

end NearQuarticWires.StageColumns
