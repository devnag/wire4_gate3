import Proof.Quartic.StageNativeKidsPool.Budget
import Proof.Quartic.StageNativeKidsPrice.Final

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKidsPoolPrice

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.CompilerMachine
open StageNativeKids StageNativeKidsPrice StageNativeKidsPool StageTuple StagePrint

/-- `imp:disjoint` and `prop:time`, paper/paper.tex: the actual complete row loop retains the
unchanged original sharp child cap in its structural resource. -/
theorem count_le_scale (a : SourceCase) : (actualFamily a).count ≤ a.scale := by
  have h:=a.request.originalKids_cap
  rw [a.request.toRowContext.nativeKids_length] at h
  change (actualFamily a).count ≤ _ at h
  unfold SourceCase.scale NativeKidsRequest.originalSourceScale
  omega

theorem count_price : Price SourceCase.scale (fun a=>(actualFamily a).count) :=
  Price.of_le count_le_scale

/-- `prop:time`, paper/paper.tex: the
target field width is charged only by its actual encoded source
bytes, without bounding or decoding its numeric value. -/
theorem width_codec_price : Price SourceCase.scale
    (fun a=>(natWord a.request.outputWidth).length) := by
  apply Price.of_le
  intro a
  have hw : (natWord a.request.outputWidth).length ≤ a.request.word.length := by
    simp [NativeKidsRequest.word,NativeKidsRequest.sourceFields,Top.loadRec,frame_length]
    omega
  unfold SourceCase.scale NativeKidsRequest.originalSourceScale
  omega

theorem count_codec_price : Price SourceCase.scale
    (fun a=>(natWord (actualFamily a).count).length) := by
  have hc:=count_price
  have h : Price SourceCase.scale (fun a=>2*((actualFamily a).count+1)+1) := by
    price_with scale_pos
  apply h.mono
  intro a
  rw [NearCubicGates.Close.Dispatch.natWord_length]
  have hn:=NearCubicGates.Close.Dispatch.natBitLength_le_succ (actualFamily a).count
  omega

theorem header_price : Price SourceCase.scale (fun a=>(actualFamily a).header.length) := by
  have hn:=arity_price
  have h : Price SourceCase.scale (fun a=>1000*(a.request.header.call.n+1)^4) := by
    price_with scale_pos
  exact h.mono fun a=>header_length a.request.toRowContext a.request.atom

theorem source_price : Price SourceCase.scale (fun a=>(actualFamily a).source.length) :=
  source_word_price

theorem index_price : Price RowCase.scale (fun b=>b.childIndex.val) := by
  apply Price.of_le
  intro b
  exact b.childIndex.isLt.le.trans (count_le_scale b.toSourceCase)

end NearQuarticWires.StageNativeKidsPoolPrice
