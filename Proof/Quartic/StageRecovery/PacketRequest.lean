import Proof.Quartic.StageRecovery.PacketFields
import Proof.Gates.WorkerArith.GuessWordLengths
import Proof.Gates.CounterMachine.PrefixRun

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open NearCubicGates.Close.WorkerArith.WorkerBounds (nbl_le_of_lt nbl_le_self)

/-- `lem:print`, paper/paper.tex: a bounded native table
packet and positive recovery modulus. Values are nonnegative because
the native cut coefficients have already been reduced. -/
structure PacketRequest where
  width : ℕ
  modulus : ℕ
  values : List ℕ
  modulus_pos : 0 < modulus
  values_fit : ∀ value ∈ values, 2 * value < 2 ^ width

/-- `prop:time`, paper/paper.tex: binary workspace grows
with packet width and the bit lengths of the modulus and entry count. -/
def PacketRequest.hint (r : PacketRequest) : ℕ :=
  r.width + natBitLength r.modulus + natBitLength r.values.length + 8

/-- `lem:print`, paper/paper.tex: the decoder reads an
internal width header followed by the actual unchanged native packet. -/
def PacketRequest.word (r : PacketRequest) : List Bool :=
  natWord r.hint ++ natWord r.modulus ++ natWord r.values.length ++ packetStream r.width r.values

/-- `lem:print`, paper/paper.tex: the required exact
output list, retaining all native row and column positions. -/
def PacketRequest.output (r : PacketRequest) : List Bool :=
  listWord intWord (r.values.map fun value : ℕ => Walks.centeredResidue r.modulus value)

/-- `prop:time`, paper/paper.tex: the sign field always
has exactly one bit of natural-codec payload. -/
theorem naturalSign_bits (q value : ℕ) : natBitLength (naturalSign q value) = 1 := by
  unfold naturalSign
  split <;> norm_num [natBitLength]

/-- `lem:residue`, paper/paper.tex: centered magnitudes do not
exceed the positive modulus, including the positive endpoint. -/
theorem naturalMagnitude_le (q value : ℕ) (hq : 0 < q) : naturalMagnitude q value ≤ q := by
  unfold naturalMagnitude
  split
  · exact Nat.sub_le _ _
  · exact (Nat.mod_lt _ hq).le

/-- `prop:time`, paper/paper.tex: every centered output
magnitude fits within the modulus's actual binary width. -/
theorem PacketRequest.magnitude_bits (r : PacketRequest) (value : ℕ) :
    natBitLength (naturalMagnitude r.modulus value) ≤ natBitLength r.modulus := by
  apply NearCubicGates.Close.WorkerArith.WorkerBounds.nbl_le_of_lt
    (by unfold natBitLength; omega)
  exact lt_of_le_of_lt (naturalMagnitude_le _ _ r.modulus_pos) (lt_natBitLength _)

/-- `prop:time`, paper/paper.tex: each record has a
uniform bit-width budget independent of the number of outer centers. -/
theorem PacketRequest.entry_cost (r : PacketRequest) (value : ℕ) :
    packetEntryCost r.width r.modulus value ≤ 200 * (r.hint + 1) := by
  have hb := r.magnitude_bits value
  simp only [packetEntryCost, naturalSign_bits]
  unfold PacketRequest.hint
  omega

/-- `prop:time`, paper/paper.tex: no subroutine call is
made by the binary packet decoder. -/
noncomputable def packetCallee : Callee :=
  ⟨Empty, fun e => e.elim, fun e => e.elim, fun e => e.elim,
    wordFunction_of_wmx (NearCubicGates.Close.WordPrograms.WMX.skip :
      NearCubicGates.Close.WordPrograms.WMX 1 0) 1 (by decide) (fun _ => 0) (fun e => e.elim)⟩

/-- `prop:time`, paper/paper.tex: workspace is within a
fixed linear factor of the decoded width hint. -/
def packetSizes : Sz := ⟨64, 1, 0, 0, 0, 0⟩

/-- `prop:time`, paper/paper.tex: the cold physical
context obtains enough binary arithmetic width from its actual header. -/
theorem PacketRequest.context_width (r : PacketRequest) :
    64 * (r.hint + 1) ≤ (ctxOf packetCallee packetSizes r.word).Wd := by
  have hl : leadOnes r.word = natBitLength r.hint := by
    unfold PacketRequest.word
    simpa only [List.append_assoc] using
      NearCubicGates.Close.CounterMachine.PrefixProg.leadOnes_natWord r.hint
        (natWord r.modulus ++ natWord r.values.length ++ packetStream r.width r.values)
  change 64 * (r.hint + 1) ≤ 2 ^ (1 * leadOnes r.word) * 64
  rw [hl, Nat.one_mul]
  have h := lt_natBitLength r.hint
  omega

end NearQuarticWires.StageRecovery
