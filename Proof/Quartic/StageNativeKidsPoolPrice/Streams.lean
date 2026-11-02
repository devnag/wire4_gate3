import Proof.Quartic.StageNativeKidsPoolPrice.Resources
import Proof.Quartic.Control.GammaControl

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKidsPoolPrice

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open StageNativeKids StageNativeKidsPrice StageNativeKidsPool StageTuple StagePrint

/-- `lem:print`, paper/paper.tex: the
actual sequential row suffix has its literal finite byte sum, including
empty pools, with no supplied table or maximum-row-size premise. -/
theorem suffix_length_le (bytes : ℕ→List Bool) (B : ℕ) (h : ∀j,(bytes j).length ≤ B)
    (j left : ℕ) : (suffix bytes j left).length ≤ left*B := by
  induction left generalizing j with
  | zero=>simp [suffix]
  | succ left ih=>
    have hj:=h j
    have ht:=ih (j+1)
    simp only [suffix,List.length_append,Nat.succ_mul]
    omega

/-- `prop:time`, paper/paper.tex: every
actual row's output bytes are bounded by that SAME real pipeline
clock, derived from its closed ordinary word-function realization. -/
theorem row_bytes_le (a : SourceCase) (j : Children a) :
    ((pipelineRecords (rowRequest a j)).flatMap frame).length ≤ (rowRequest a j).budget+1 :=
  Control.output_length_le (pipelineRecordPrinter a.second) (rowRequest a j)

/-- `prop:time`, paper/paper.tex: the
complete actual answer's count codec, copied target-width codec,
all real row bytes and final delimiter have one structural price. -/
theorem answer_price : Price SourceCase.scale (fun a=>(actualAnswer a).length) := by
  obtain ⟨K,e,he⟩:=StageNativeKidsPrice.row_price
  have hc:=count_price
  have hcc:=count_codec_price
  have hw:=width_codec_price
  have hscale:=Price.identity SourceCase.scale
  have h : Price SourceCase.scale (fun a=>(natWord (actualFamily a).count).length+
      (natWord a.request.outputWidth).length+(actualFamily a).count*(K*a.scale^e+1)+1) := by
    price_with scale_pos
  apply h.mono
  intro a
  have hbytes (j : ℕ) : ((actualFamily a).bytes pipelineRecords j).length ≤ K*a.scale^e+1 := by
    by_cases hj : j<(actualFamily a).count
    · simp only [Family.bytes,dif_pos hj]
      exact (row_bytes_le a ⟨j,hj⟩).trans
        (Nat.add_le_add_right (he (RowCase.mk a ⟨j,hj⟩)) 1)
    · simp only [Family.bytes,dif_neg hj,List.length_nil]
      omega
  have hs:=suffix_length_le ((actualFamily a).bytes pipelineRecords) (K*a.scale^e+1) hbytes 0 (actualFamily a).count
  simp only [actualAnswer,List.length_append,List.length_singleton]
  omega

end NearQuarticWires.StageNativeKidsPoolPrice
