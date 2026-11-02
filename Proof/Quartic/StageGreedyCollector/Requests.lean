import Proof.Quartic.StageGreedyCollector.EntryBounds
import Proof.Quartic.StageNativeWidth.NativeCuts
import Proof.Quartic.StageModularSetup.Printer

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyCollector

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5
open NearCubicGates.Close.Cells
open NearCubicWires.WireExponent3_5.CompilerMachine
open StagePrint

/-- `lem:print`, paper/paper.tex: the actual
per-walk equality request uses the original common generator and
its own proved census, before joining any other walk. -/
noncomputable def equalityRequest {B1 B2 : ℕ} (r : GreedyEntry.Request B1 B2) : NativeStreamRequest where
  parameters:=r.rowContext.header.prepared.starParams
  fieldWidth:=r.termRequest.stackWidth
  cuts:=nativeEqualityCuts r.termRequest
  lengths:=nativeEqualityCuts_lengths r.termRequest
  fits:=StageNativeWidth.nativeEqualityCuts_fits r.termRequest
  square:=entry_cuts_square r

/-- `lem:residue` and `lem:print`, paper/paper.tex: the modular request contains both actual signed weak
cuts after the equality split, at exactly one added magnitude bit. -/
noncomputable def modularRequest {B1 B2 : ℕ} (r : GreedyEntry.Request B1 B2) :
    Downstream.ModularCutsRequest where
  width:=PrimT.C4Geo.width r.rowContext.header.prepared.starParams
  fieldWidth:=r.termRequest.stackWidth+1
  modulus:=r.modulus
  cuts:=EquationRow.doubled false (nativeEqualityCuts r.termRequest)
  modulus_two:=Reconstruct.PrintRequest.two_le_modulus r.source
  modulus_fit:=by
    have hb:=StageNativeWidth.packedBits_coefficient r.rowContext.nativeFieldWidth
      (2*PrimT.C4Geo.width r.rowContext.header.prepared.starParams) r.degree r.coefficientBits
    change r.coefficientBits≤r.termRequest.stackWidth at hb
    exact (lt_natBitLength r.modulus).le.trans
      (Nat.pow_le_pow_right (by decide) (hb.trans (by omega)))
  lengths:=(equalityRequest r).matrix.lengths
  fits:=(equalityRequest r).matrix.fits

/-- `lem:print`, paper/paper.tex: the real
Tuple output is exactly the raw equality source of its next call. -/
theorem equalityRequest_input {B1 B2 : ℕ} (r : GreedyEntry.Request B1 B2) :
    Downstream.equalityRowsInput (equalityRequest r)=
      Top.loadRec r.termRequest.output
        (List.replicate (PrimT.C4Geo.width r.rowContext.header.prepared.starParams) true)
        (List.replicate r.termRequest.stackWidth true) [] [] [] [] [] [] [] [] := by
  unfold Downstream.equalityRowsInput equalityRequest
  rw [nativeEqualityCuts_word]

/-- `lem:residue` and `lem:print`, paper/paper.tex: the equality reply is precisely the signed input
stream of modular reduction, with no reduction before the split. -/
theorem modularRequest_stream {B1 B2 : ℕ} (r : GreedyEntry.Request B1 B2) :
    frame (modularRequest r).stream=Downstream.equalityRowsOutput (equalityRequest r) := by
  rfl

/-- `lem:print`, paper/paper.tex: every reduced
walk body uses the single common output field width and the original
selected modulus, with unchanged affine predicates and order. -/
theorem modularRequest_output {B1 B2 : ℕ} (r : GreedyEntry.Request B1 B2) :
    (modularRequest r).output=
      frame ((GreedyCollector.walkCuts r.source r.index).flatMap
        (MatrixScoreBatch.cutWord (GreedyCollector.fieldWidth r.source))) := by
  change frame (((EquationRow.doubled false (nativeEqualityCuts r.termRequest)).map
    (StageRecovery.reduceCut r.modulus)).flatMap
      (MatrixScoreBatch.cutWord (r.termRequest.stackWidth+1)))=_
  rw [r.fieldWidth_eq]
  rfl

end NearQuarticWires.StageGreedyCollector
