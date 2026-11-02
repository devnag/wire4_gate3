import Proof.Quartic.StageCertNative.PriceEntry
import Proof.Quartic.StageCertNative.TermNative
import Proof.Quartic.StageNativeWidth.Polynomial

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5
open NearCubicGates.Close.Cells
open StageCert.Tokens

theorem price_sizingMagnitude (B1 B2 : ℕ) :
    JobPrice (fun r : TermJob B1 B2=>(exactEntry r.moment).sizingMagnitude) 0 :=
  JobPrice.of_arity ⟨entrySizingCoefficient B1 B2,entrySizingExponent B1 B2,exactEntry_sizing⟩

theorem price_stackWidth (B1 B2 : ℕ) :
    JobPrice (fun r : TermJob B1 B2=>(termRequest r.base r.index).stackWidth) 0 := by
  refine (price_sizingMagnitude B1 B2).mono ?_
  intro r
  change (exactEntry r.moment).termRequest.stackWidth≤(exactEntry r.moment).sizingMagnitude
  rw [StagePrint.EntryFormat.Request.stackWidth_actual]
  unfold StagePrint.NativeWidth.packedBits StagePrint.EntryFormat.Request.sizingMagnitude
  dsimp only
  omega

noncomputable def jobNativeWidth {B1 B2 : ℕ} (r : TermJob B1 B2) : ℕ :=
  PrimT.C4Geo.width r.moment.rules.starParams

theorem price_nativeWidth (B1 B2 : ℕ) : JobPrice (@jobNativeWidth B1 B2) 0 :=
  (price_arity B1 B2).mono (fun r=>(StageNativeWidth.nativeDimensions_le r.moment.nativeContext).1)

private theorem cutStream_length (W width : ℕ) (cuts : List MatrixScoreBatch.Cut)
    (hl : ∀c∈cuts,c.leftWeights.length=width ∧ c.rightWeights.length=width) :
    (cuts.flatMap (MatrixScoreBatch.cutWord W)).length≤
      cuts.length*((2*width+2)*(2*W+3)) := by
  simp only [List.length_flatMap]
  have hh:=List.sum_le_card_nsmul (cuts.map fun c=>(MatrixScoreBatch.cutWord W c).length)
    ((2*width+2)*(2*W+3)) (by
      intro v hv
      obtain ⟨c,hc,rfl⟩:=List.mem_map.mp hv
      obtain ⟨hL,hR⟩:=hl c hc
      simp only [MatrixScoreBatch.cutWord,MatrixScoreBatch.fields,List.length_flatMap,
        frame_length,MatrixScoreBatch.signMagnitude_length,List.map_const',List.sum_replicate,
        List.length_append,List.length_cons,List.length_nil,hL,hR,smul_eq_mul]
      exact le_of_eq (by ring))
  simpa only [List.length_map,smul_eq_mul] using hh

theorem price_termCutCount (B1 B2 : ℕ) :
    JobPrice (fun r : TermJob B1 B2=>(termNativeRequest r).cuts.length) 1 := by
  refine ⟨1,0,fun r=>?_⟩
  have hh:=termCuts_count r.base r.index
  change (termNativeRequest r).cuts.length≤
    r.moment.selected.1.Uocc^r.moment.packet.degree at hh
  simpa only [pow_zero,one_mul] using hh

theorem price_tupleOutput (B1 B2 : ℕ) :
    JobPrice (fun r : TermJob B1 B2=>(termRequest r.base r.index).output.length) 1 := by
  have hw:=((JobPrice.constant 2).mul (price_nativeWidth B1 B2)).add (JobPrice.constant 2)
  have hp:=((JobPrice.constant 2).mul (price_stackWidth B1 B2)).add (JobPrice.constant 3)
  have hh:=(price_termCutCount B1 B2).mul (hw.mul hp)
  refine hh.mono ?_
  intro r
  rw [←StagePrint.nativeEqualityCuts_word]
  exact cutStream_length _ _ _ (termNativeRequest r).lengths

theorem price_termWeakLength (B1 B2 : ℕ) :
    JobPrice (fun r : TermJob B1 B2=>(termWeakWord r).length) 1 := by
  have hw:=((JobPrice.constant 2).mul (price_nativeWidth B1 B2)).add (JobPrice.constant 2)
  have hp:=((JobPrice.constant 2).mul ((price_stackWidth B1 B2).add
    (JobPrice.constant 1))).add (JobPrice.constant 3)
  have hh:=((JobPrice.constant 2).mul (price_termCutCount B1 B2)).mul (hw.mul hp)
  refine hh.mono ?_
  intro r
  have he:=cutStream_length ((termNativeRequest r).fieldWidth+1) (jobNativeWidth r)
    (EquationRow.doubled false (termNativeRequest r).cuts)
    (by
      intro c hc
      exact (termNativeRequest r).matrix.lengths c hc)
  rw [EquationRow.doubled_length] at he
  exact he

end NearQuarticWires.StageCertNative
