import Proof.Quartic.StageCertificateControl.InputTest
import Proof.Quartic.StageCertTests.NativeSigned

/-!
# The exact signed native table as one certificate test

Paper: `lem:print`, paper/paper.tex,
`eq:testX`–`eq:testPhi`, and Step 2.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageCertificateFinal

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.WordPrograms.SInt (encS)
open StageCertificateControl (NativeTest)

/-- `lem:print` and `sec:algorithm`, paper/paper.tex: the actual native table contributes its entire
signed census and literal native width to one strict certificate test. -/
def tableTest (bound : ℕ) (table : StagePrint.TableRequest) : NativeTest where
  bound := bound
  width := (StageCertTests.nativeSignedRequest table).width
  values := (StageCertTests.nativeSignedRequest table).values

/-- `lem:print`, paper/paper.tex: a strict
test has exactly its threshold, actual width header, and unchanged
complete native output bytes, including the final record delimiter. -/
theorem tableTest_word (bound : ℕ) (table : StagePrint.TableRequest) :
    (tableTest bound table).word=natWord bound++natWord (table.q+1)++table.output := by
  change natWord bound++natWord (table.q+1)++StageCertTests.signedStream
    (StageCertTests.nativeSignedRequest table).width (StageCertTests.nativeSignedRequest table).values=_
  rw [StageCertTests.nativeSignedRequest_stream]

/-- `lem:print` and `sec:algorithm`, paper/paper.tex: the actual strict test retains every padded
native column before the sole final original-column crop. -/
theorem tableTest_count (bound : ℕ) (table : StagePrint.TableRequest) :
    (tableTest bound table).values.length=table.count :=
  StageCertTests.nativeSignedRequest_count table

/-- `lem:print`, paper/paper.tex: every signed
native value fits the physically emitted width, independently of any
column certificate or hypothesis about the witness. -/
theorem tableTest_values_fit (bound : ℕ) (table : StagePrint.TableRequest) :
    ∀z∈(tableTest bound table).values,encS z<2^(tableTest bound table).width :=
  (StageCertTests.nativeSignedRequest table).values_fit

end NearQuarticWires.StageCertificateFinal
