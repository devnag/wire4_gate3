import Proof.Quartic.StageCertTests.SignedCost
import Proof.Quartic.StagePrint.FullTable
import Proof.Quartic.StageRecovery.TablePacket

set_option autoImplicit false

namespace NearQuarticWires.StageCertTests

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.TabMachine NearCubicGates.Close.Interfaces
open NearCubicGates.Close.WordPrograms.SInt (encS encS_lt)

/-- `lem:print`, paper/paper.tex:
the actual signed native table determines its exact decoder request. -/
def nativeSignedRequest (r : StagePrint.TableRequest) : SignedRequest where
  width := r.q+1
  values := pvals false (StagePrint.cutTable r.matrix)
  values_fit := by
    intro z hz
    obtain ⟨i,j,rfl⟩ := StageRecovery.mem_pvals_false _ z hz
    exact encS_lt ((r.value_bound i j).trans_le
      (Nat.pow_le_pow_right (by decide) (Nat.sub_le r.q 1)))

/-- `lem:print`, paper/paper.tex:
the native packet is literally the signed decoder's record suffix. -/
theorem nativeSignedRequest_stream (r : StagePrint.TableRequest) :
    signedStream (nativeSignedRequest r).width (nativeSignedRequest r).values = r.output := rfl

/-- `lem:print`, paper/paper.tex:
all actual native signed entries are retained, including padded positions. -/
theorem nativeSignedRequest_count (r : StagePrint.TableRequest) :
    (nativeSignedRequest r).values.length = r.count := by
  simpa only [StageRecovery.tableNaturals,List.length_map,nativeSignedRequest]
    using StageRecovery.tableNaturals_length r

/-- `prop:time`, paper/paper.tex:
the actual signed native decoder's complete physical clock is linear
in the native census, with polynomial binary-dimension dependence. -/
theorem nativeSignedRequest_budget (r : StagePrint.TableRequest) :
    (nativeSignedRequest r).budget ≤
      10^12 * (NearCubicGates.Close.Cells.TSK StageRecovery.packetCallee+10) *
        (r.count+1) * (r.q+natBitLength r.count+10)^4 := by
  have h := (nativeSignedRequest r).budget_le
  have he : (nativeSignedRequest r).hint+1 = r.q+natBitLength r.count+10 := by
    change r.q+1+natBitLength (nativeSignedRequest r).values.length+8+1 = _
    rw [nativeSignedRequest_count]
    omega
  simpa only [nativeSignedRequest_count,he] using h

/-- `lem:print` and `sec:algorithm`, paper/paper.tex: the canonical signed table
is produced by the actual cold decoder at the exact native table ABI. -/
noncomputable def nativeSignedMachine :
    WordFunction StagePrint.TableRequest
      (fun r => (nativeSignedRequest r).word)
      (fun r => listWord intWord
        (pvals false (StagePrint.cutTable r.matrix)))
      (fun r => (nativeSignedRequest r).budget) where
  program := signedWordFunction.program
  realizes := by
    intro r
    exact signedWordFunction.realizes (nativeSignedRequest r)

end NearQuarticWires.StageCertTests
