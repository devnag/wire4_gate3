import Proof.Quartic.StageCertificateControl.PayloadFold
import Proof.Quartic.StagePrint.PoolAvoids

/-!
# The counted whole-table pool finalizer

Paper: complete native tables in `lem:print`, paper/paper.tex, and `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close NearCubicGates.Close.WordPrograms

/-- The scalar test-count writer of `sec:algorithm`, paper/paper.tex, reads the actual completed pool index, shares the final
output cursor, and uses six separate zero scratch registers. -/
def flattenWriterRegs : Fin 8 ↪ Fin 16 :=
  ⟨![4,5,6,7,8,9,10,12],by decide⟩

/-- The exact input of the test fold in `sec:algorithm`,
paper/paper.tex, retains the original preparation,
a physically written test count, and every native test payload. -/
def flattenedPoolWord (source : List Bool) (cache : ℕ→List Bool) (count : ℕ) : List Bool :=
  source++NearCubicWires.RepairRepresentation.natWord count++(List.range count).flatMap cache

/-- The whole native-table pool of `lem:print` and `prop:time`,
paper/paper.tex, is copied
with one marked-payload scan per actual cache. The count header
comes from its completed index register, and both head returns
are charged by their real counters. -/
def flattenPoolProgram (p : Program) : WMX (p.tapeCount+5) 16 :=
  .seq (.wm (NearCubicWires.WireExponent3_5.FinalPass.Hash4.wcopyR 13 15 14))
    (.seq (.wm (WM.rewind (StagePrint.poolOutput p) 15))
      (.seq (copyPayload (StagePrint.poolSource p) (StagePrint.poolFinal p) 12 15)
        (.seq (.wm (writeNatM (StagePrint.poolFinal p) flattenWriterRegs))
          (.seq (.wm (NearCubicWires.WireExponent3_5.FinalPass.Hash4.wcopyR 4 14 11))
            (.seq (copyPayloads (StagePrint.poolOutput p) (StagePrint.poolFinal p) 12 15 14)
              (.wm (emitC (StagePrint.poolFinal p) 12 false)))))))

/-- The actual finite register capacity of `prop:time`,
paper/paper.tex, is linear in the original
preparation, completed cache bytes, and polynomial test census. -/
def flattenPoolCapacity (sourceLength cacheBytes count : ℕ) : ℕ :=
  100*(sourceLength+cacheBytes+count+1)

/-- The final native pool scan of `prop:time`, paper/paper.tex, has linear cache-byte work and a polynomial
scalar-header term, without squaring the native output length. -/
def flattenPoolCost (sourceLength cacheBytes count : ℕ) : ℕ :=
  1000*(sourceLength+cacheBytes+1)+10000*(count+1)^2

end NearQuarticWires.StageCertificateControl
