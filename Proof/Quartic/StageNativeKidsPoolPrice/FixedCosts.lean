import Proof.Quartic.StageNativeKidsPoolPrice.Resources

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKidsPoolPrice

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.CompilerMachine
open StageNativeKids StageNativeKidsPrice StageNativeKidsPool StageTuple StagePrint

/-- `prop:time`, paper/paper.tex: the
fixed loader is priced by the actual two retained source byte streams
and the encoded width field, never by the numeric target width. -/
theorem loader_price : Price SourceCase.scale (fun a=>
    Top.loadCost (frame (actualFamily a).source) (frame (actualFamily a).header)
      (natWord a.request.outputWidth) [] [] [] [] [] [] [] []) := by
  have hs:=source_price
  have hh:=header_price
  have hw:=width_codec_price
  simp only [Top.loadCost,Top.loadRec,Top.loadChainCost,List.length_append,frame_length,List.length_nil]
  price_with scale_pos

theorem counter_copy_price : Price SourceCase.scale
    (fun a=>counterCopyCost (actualFamily a).source) := by
  have hs:=source_price
  unfold counterCopyCost
  price_with scale_pos

/-- `prop:time`, paper/paper.tex: the
actual bounded-child initialization includes its true quadratic child
clock and scans of both actual finite binary codecs. -/
theorem initialize_price : Price SourceCase.scale
    (fun a=>initializeCost (actualFamily a).count a.request.outputWidth) := by
  have hc:=count_price
  have hcc:=count_codec_price
  have hw:=width_codec_price
  unfold initializeCost
  price_with scale_pos

end NearQuarticWires.StageNativeKidsPoolPrice
