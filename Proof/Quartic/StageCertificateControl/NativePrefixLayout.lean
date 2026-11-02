import Proof.Quartic.StageCertificateControl.IndexedLayout

/-!
# Retain a binary threshold header around an actual native table call

Paper: `eq:testX`–`eq:testPhi`, paper/paper.tex,
`lem:print`, and `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.CopyNat
open NearCubicGates.Close NearCubicGates.Close.WordPrograms

/-- `prop:time`, paper/paper.tex: preparation
copying has its own actual output count and restored scratch registers. -/
def nativePrefixPreparationRegs : Fin 4 ↪ Fin 32 := ⟨![7,11,12,13],by decide⟩

/-- `prop:time`, paper/paper.tex: the first
binary natural field is retained without numeric decoding; only the
remaining literal source bytes are copied into the real table bank. -/
def nativePrefixLoadProgram (p : Program) : WMX (p.tapeCount+11) 32 :=
  .seq (.wm (copyNatM true (indexedExternal p 0) (indexedExternal p 1) 0 1 4))
    (.seq (.wm (finishMarkedCopy (indexedExternal p 1) 4 5 6))
      (copyPreparation (indexedExternal p 0) (indexedSite p).input nativePrefixPreparationRegs))

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual whole native table is
called once, copied unchanged, and erased. Its real copied-byte count
then drives the retained output's physical head return. -/
noncomputable def nativePrefixCallProgram (p : Program) : WMX (p.tapeCount+11) 32 :=
  .seq (StagePrint.callAppendProgram (indexedSite p) (indexedExternal p 2) 14)
    (.wm (WM.rewind (indexedExternal p 2) 14))

/-- `prop:time`, paper/paper.tex: marker-
driven copies prefix the unchanged native payload with the retained
binary threshold code and write one final delimiter. -/
def nativePrefixEmitProgram (p : Program) : WMX (p.tapeCount+11) 32 :=
  .seq (copyPayload (indexedExternal p 1) (indexedFinal p) 19 20)
    (.seq (copyPayload (indexedExternal p 2) (indexedFinal p) 19 20)
      (.wm (emitC (indexedFinal p) 19 false)))

/-- `eq:testX`–`eq:testPhi`, `lem:print`, and `prop:time`,
paper/paper.tex:
the fixed wrapper retains the actual threshold header around one
actual whole-table computation, preserving every signed native byte. -/
noncomputable def nativePrefixProgram (p : Program) : WMX (p.tapeCount+11) 32 :=
  .seq (nativePrefixLoadProgram p) (.seq (nativePrefixCallProgram p) (nativePrefixEmitProgram p))

end NearQuarticWires.StageCertificateControl
