import Proof.Quartic.StageCertTests.SignedList
import Proof.Quartic.StageRecovery.PacketRequest

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertTests

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open NearCubicGates.Close.WordPrograms.SInt (encS)
open NearCubicGates.Close.WorkerArith.WorkerBounds (nbl_le_of_lt nbl_le_self)
open StageRecovery (packetCallee packetSizes)

/-- `lem:print`, paper/paper.tex:
a native table packet may contain arbitrary signed moments. -/
structure SignedRequest where
  width : ℕ
  values : List ℤ
  values_fit : ∀ z ∈ values, encS z < 2 ^ width

/-- `prop:time`, paper/paper.tex:
arithmetic width depends on record width and the binary entry count. -/
def SignedRequest.hint (r : SignedRequest) : ℕ :=
  r.width + natBitLength r.values.length + 8

/-- `lem:print`, paper/paper.tex:
the converter reads a bounded internal header and the unchanged native stream. -/
def SignedRequest.word (r : SignedRequest) : List Bool :=
  natWord r.hint ++ natWord 0 ++ natWord r.values.length ++ signedStream r.width r.values

/-- `sec:algorithm`, paper/paper.tex:
the exact signed output retains every native table position. -/
def SignedRequest.output (r : SignedRequest) : List Bool := listWord intWord r.values

/-- `prop:time`, paper/paper.tex:
the sign field has one bit of natural-codec payload in both branches. -/
theorem signed_sign_bits (z : ℤ) : natBitLength (if z < 0 then 1 else 0) = 1 := by
  split <;> norm_num [natBitLength]

/-- `prop:time`, paper/paper.tex:
the actual native bound controls each canonical magnitude's binary length. -/
theorem SignedRequest.magnitude_bits (r : SignedRequest) (z : ℤ) (hz : z ∈ r.values) :
    natBitLength z.natAbs ≤ r.width + 1 := by
  have he : z.natAbs ≤ encS z := by unfold encS; split <;> omega
  apply NearCubicGates.Close.WorkerArith.WorkerBounds.nbl_le_of_lt (by omega)
  exact (he.trans_lt (r.values_fit z hz)).trans_le
    (Nat.pow_le_pow_right (by decide) (Nat.le_succ _))

/-- `prop:time`, paper/paper.tex:
the exact entry clock is uniformly linear in the internal binary hint. -/
theorem SignedRequest.entry_cost (r : SignedRequest) (z : ℤ) (hz : z ∈ r.values) :
    signedEntryCost r.width z ≤ 200 * (r.hint+1) := by
  have hm := r.magnitude_bits z hz
  simp only [signedEntryCost,signed_sign_bits]
  unfold SignedRequest.hint
  omega

/-- `prop:time`, paper/paper.tex:
the cold context derives sufficient width from the actual encoded hint. -/
theorem SignedRequest.context_width (r : SignedRequest) :
    64 * (r.hint+1) ≤ (ctxOf packetCallee packetSizes r.word).Wd := by
  have hl : leadOnes r.word = natBitLength r.hint := by
    unfold SignedRequest.word
    simpa only [List.append_assoc] using
      NearCubicGates.Close.CounterMachine.PrefixProg.leadOnes_natWord r.hint
        (natWord 0 ++ natWord r.values.length ++ signedStream r.width r.values)
  change 64 * (r.hint+1) ≤ 2 ^ (1 * leadOnes r.word) * 64
  rw [hl,Nat.one_mul]
  have h := lt_natBitLength r.hint
  omega

end NearQuarticWires.StageCertTests
