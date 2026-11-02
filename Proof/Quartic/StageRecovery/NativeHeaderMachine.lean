import Proof.Quartic.StageRecovery.NativeHeaderEmit
import Proof.Gates.Expand.PolyTabPack

set_option autoImplicit false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Expand.PolyTab

/-- `prop:time`, paper/paper.tex: the header
program's finite register/output capacity includes the actual native
census and every bit of the three emitted canonical header codecs. -/
def NativeRequest.headerCapacity (r : NativeRequest) : ℕ :=
  r.table.count + r.table.q + natBitLength r.modulus + r.packet.hint +
    6 * natBitLength r.packet.hint + 2 * r.header.length + 50

/-- `lem:print`, paper/paper.tex: the complete
physical header machine starts with the unchanged literal outer record,
extracts real fields and emits the existing framed decoder header. -/
noncomputable def nativeHeaderProgram : WMX 27 10 :=
  .seq nativeMetadataProgram (.seq (.wm nativeHintProgram) (.wm nativeHeaderEmitProgram))

/-- `prop:time`, paper/paper.tex: all header
extraction, computation and physical serialization clocks add. -/
def NativeRequest.headerSteps (r : NativeRequest) : ℕ :=
  r.metadataSteps + 1 + (r.hintSteps + 1 + r.headerEmitSteps)

/-- `lem:print`, paper/paper.tex: the cold
header machine's actual output has no supplied width/count/length
tapes, and the modulus is copied as a codec rather than decoded unary. -/
theorem nativeHeaderProgram_spec (r : NativeRequest) :
    Runs r.headerCapacity nativeHeaderProgram (idealStart 27 10 r.word r.metadataLens)
      r.headerSteps (fun b => b.st 27 = frame r.header) := by
  have eM := nativeMetadataProgram_spec r.headerCapacity r
    (by unfold NativeRequest.headerCapacity; omega)
    (by unfold NativeRequest.headerCapacity; omega)
    (by unfold NativeRequest.headerCapacity; omega)
  exact eM.seq (by
    intro σ hs
    have eh := nativeHintProgram_spec r.headerCapacity r σ hs (by
      rw [r.nativeHint_eq]
      unfold NativeRequest.headerCapacity
      omega)
    exact Runs.seqE (WXExec.wm eh) (nativeHeaderEmitProgram_spec r.headerCapacity r σ hs
      (by unfold NativeRequest.headerCapacity; omega)))

/-- `prop:time`, paper/paper.tex: the cold
header word function includes the complete ordinary simulation clock. -/
def NativeRequest.headerBudget (r : NativeRequest) : ℕ := 2 * r.headerSteps + 2

/-- `lem:print`, paper/paper.tex: an actual
ordinary cold word function produces exactly the existing framed
hint/modulus/original-column-count header from its sole outer input. -/
noncomputable def nativeHeaderWordFunction :
    WordFunction NativeRequest NativeRequest.word (fun r => frame r.header) NativeRequest.headerBudget :=
  wordFunction_of_ideal nativeHeaderProgram 27 (by decide) NativeRequest.headerCapacity
    NativeRequest.metadataLens NativeRequest.headerSteps (fun _ => le_rfl) (by
      intro r
      exact ⟨by simp [NativeRequest.metadataLens], nativeHeaderProgram_spec r⟩)

end NearQuarticWires.StageRecovery
