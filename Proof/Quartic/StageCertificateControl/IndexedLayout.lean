import Proof.Quartic.StageCertificateControl.IndexedRequest
import Proof.Quartic.StageCertificateControl.SelectMetadata
import Proof.Quartic.StageCertificateControl.OpenMarked
import Proof.Quartic.StageCertificateControl.PreparationCopy
import Proof.Quartic.StagePrint.CallAppend

/-!
# The concrete indexed whole-test preprocessing program

Paper: Step 2 of `sec:algorithm`, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close NearCubicGates.Close.WordPrograms
open NearQuarticWires.Control

/-- `prop:time`, paper/paper.tex: eleven
fixed external streams are separate from the scheduler's complete
physical bank and from the final fresh output. -/
def indexedExternal (p : Program) (i : Fin 11) : Fin (p.tapeCount+12) :=
  ⟨i.val,by have := i.isLt;omega⟩

/-- `prop:time`, paper/paper.tex: the
scheduler occupies a fixed disjoint physical tape bank. -/
def indexedBank (p : Program) (j : Fin p.tapeCount) : Fin (p.tapeCount+12) :=
  ⟨11+j.val,by have := j.isLt;omega⟩

/-- `prop:time`, paper/paper.tex: the
preprocessing output is physically fresh and outside every prior stream. -/
def indexedFinal (p : Program) : Fin (p.tapeCount+12) := ⟨p.tapeCount+11,by omega⟩

/-- `prop:time`, paper/paper.tex: fixed
call scratch registers are distinct from the retained schedule index. -/
def indexedSiteRegs : Fin 4 ↪ Fin 32 := ⟨![0,1,2,3],by decide⟩

/-- `prop:time`, paper/paper.tex: the
actual scheduler call uses separate tally, guard and ruler streams. -/
def indexedSite (p : Program) : Site p (p.tapeCount+11) 32 where
  bank := indexedBank p
  tally := indexedExternal p 8
  guard := indexedExternal p 9
  ruler := indexedExternal p 10
  regs := indexedSiteRegs
  bank_inj := by
    intro i j h
    apply Fin.ext
    have hh := congrArg Fin.val h
    change 11+i.val=11+j.val at hh
    omega
  tally_ne := by intro j h;have hh := congrArg Fin.val h;change 11+j.val=8 at hh;omega
  guard_ne := by intro j h;have hh := congrArg Fin.val h;change 11+j.val=9 at hh;omega
  ruler_ne := by intro j h;have hh := congrArg Fin.val h;change 11+j.val=10 at hh;omega
  tally_guard := by intro h;have hh := congrArg Fin.val h;change 8=9 at hh;omega
  tally_ruler := by intro h;have hh := congrArg Fin.val h;change 8=10 at hh;omega
  guard_ruler := by intro h;have hh := congrArg Fin.val h;change 9=10 at hh;omega

/-- `prop:time`, paper/paper.tex: whole-record
selection and five-field copying share only their restored scratch. -/
def indexedSelectionRegs : Fin 8 ↪ Fin 32 := ⟨![0,1,2,6,7,4,8,9],by decide⟩

/-- `prop:time`, paper/paper.tex: the
complete copied schedule uses its actual frame counter. -/
def indexedScheduleRegs : Fin 6 ↪ Fin 32 := ⟨![10,11,12,13,14,15],by decide⟩

/-- `prop:time`, paper/paper.tex: selected
metadata is unframed by its preserved actual marked-byte count. -/
def indexedMetadataRegs : Fin 6 ↪ Fin 32 := ⟨![7,11,12,13,14,16],by decide⟩

/-- `prop:time`, paper/paper.tex: threshold
extraction has separate discard and retained-header counters. -/
def indexedThresholdRegs : Fin 5 ↪ Fin 32 := ⟨![0,1,2,17,18],by decide⟩

/-- `prop:time`, paper/paper.tex: the
original preparation copy uses four restored registers outside the index. -/
def indexedPreparationRegs : Fin 4 ↪ Fin 32 := ⟨![21,22,23,24],by decide⟩

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: only the bounded numeric schedule index is
decoded; the preparation suffix is copied at its actual current offset. -/
def indexedLoadProgram (p : Program) : WMX (p.tapeCount+11) 32 :=
  .seq (.wm (readNatM true (indexedExternal p 0) 0 1 4 2 3))
    (copyPreparation (indexedExternal p 0) (indexedSite p).input indexedPreparationRegs)

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: the real framed scheduler runs once, is
erased, and its actual output bytes determine the selected record. -/
noncomputable def indexedScheduleProgram (p : Program) : WMX (p.tapeCount+11) 32 :=
  .seq (StagePrint.callAppendProgram (indexedSite p) (indexedExternal p 1) 10)
    (.seq (.wm (openCopiedFrame (indexedExternal p 1) (indexedExternal p 2) indexedScheduleRegs))
      (.seq (.wm (WM.rewind (indexedExternal p 2) 15))
        (selectMetadata (indexedExternal p 2) (indexedExternal p 3) (indexedExternal p 4)
          indexedSelectionRegs)))

/-- `prop:time`, paper/paper.tex: the
selected metadata remains available for the base request while its
actual fifth binary field is copied into a separate framed header. -/
def indexedThresholdProgram (p : Program) : WMX (p.tapeCount+11) 32 :=
  .seq (.wm (measuredUnframe (indexedExternal p 4) (indexedExternal p 5) indexedMetadataRegs))
    (.seq (.wm (WM.rewind (indexedExternal p 5) 16))
      (.seq (.wm (NearCubicWires.WireExponent3_5.FinalPass.Hash4.wcopyR 7 11 12))
        (.seq (.wm (WM.rewind (indexedExternal p 4) 11))
          (.seq (copyThresholdFields (indexedExternal p 5) (indexedExternal p 3) (indexedExternal p 6)
              indexedThresholdRegs)
            (.wm (finishMarkedCopy (indexedExternal p 6) 18 8 9))))))

/-- `prop:time`, paper/paper.tex: three
actual marker-driven copies write the threshold header, unchanged
preparation, and selected metadata before the final delimiter. -/
def indexedEmitProgram (p : Program) : WMX (p.tapeCount+11) 32 :=
  .seq (copyPayload (indexedExternal p 6) (indexedFinal p) 19 20)
    (.seq (copyPayload (indexedExternal p 0) (indexedFinal p) 19 20)
      (.seq (copyPayload (indexedExternal p 4) (indexedFinal p) 19 20)
        (.wm (emitC (indexedFinal p) 19 false))))

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: the fixed whole-test preprocessing program
contains actual index decoding, a physical scheduler call, measured
record selection, binary threshold copying, and literal output framing. -/
noncomputable def indexedFrontProgram (p : Program) : WMX (p.tapeCount+11) 32 :=
  .seq (indexedLoadProgram p) (.seq (indexedScheduleProgram p)
    (.seq (indexedThresholdProgram p) (indexedEmitProgram p)))

/-- `prop:time`, paper/paper.tex: every
external stream is distinct from every actual scheduler-bank tape. -/
theorem indexedBank_external_ne (p : Program) (j : Fin p.tapeCount) (i : Fin 11) :
    indexedBank p j≠indexedExternal p i := by
  intro h
  have hh := congrArg Fin.val h
  have hi := i.isLt
  change 11+j.val=i.val at hh
  omega

/-- `prop:time`, paper/paper.tex: final
output freshness holds for every external stream and every bank tape. -/
theorem indexedFinal_fresh (p : Program) :
    (∀ i : Fin 11,indexedExternal p i≠indexedFinal p) ∧
      (∀ j : Fin p.tapeCount,indexedBank p j≠indexedFinal p) := by
  have hp := p.twoTapes
  constructor
  · intro i h
    have hh := congrArg Fin.val h
    have hi := i.isLt
    change i.val=p.tapeCount+11 at hh
    omega
  · intro j h
    have hh := congrArg Fin.val h
    have hj := j.isLt
    change 11+j.val=p.tapeCount+11 at hh
    omega

end NearQuarticWires.StageCertificateControl
