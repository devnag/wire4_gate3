import Proof.Quartic.StageCertTests.SignedMachine
import Proof.Gates.CounterMachine.PrefixFinal

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertTests

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open StageRecovery (packetCallee packetSizes)

/-- `prop:time`, paper/paper.tex:
the complete signed native source has linear length in table count
and actual field width. -/
theorem SignedRequest.word_length_le (r : SignedRequest) :
    r.word.length ≤ 10 * (r.values.length+1) * (r.hint+1) := by
  have hn : natBitLength r.values.length ≤ r.hint := by unfold SignedRequest.hint;omega
  have hw : r.width ≤ r.hint := by unfold SignedRequest.hint;omega
  have hh := NearCubicGates.Close.WorkerArith.WorkerBounds.nbl_le_self r.hint
  have hs : (signedStream r.width r.values).length = r.values.length * (2*r.width+1)+1 := by
    unfold signedStream
    rw [NearCubicGates.Close.WordPrograms.recStream_length r.width _
      (by intro w hw;obtain ⟨z,_,rfl⟩ := List.mem_map.mp hw;simp)]
    simp
  simp only [SignedRequest.word,List.length_append,natWord_length,hs]
  simp only [show natBitLength 0 = 1 from rfl]
  nlinarith

/-- `prop:time`, paper/paper.tex:
the exact signed converter source clock is linear in table count
and polynomial only in binary dimensions. -/
theorem SignedRequest.steps_le (r : SignedRequest) :
    r.steps ≤ 1000 * (r.values.length+1) * (r.hint+1) := by
  have hn : natBitLength r.values.length ≤ r.hint := by unfold SignedRequest.hint;omega
  have hh := NearCubicGates.Close.WorkerArith.WorkerBounds.nbl_le_self r.hint
  unfold SignedRequest.steps
  simp only [show natBitLength 0 = 1 from rfl]
  nlinarith

/-- `prop:time`, paper/paper.tex:
the cold binary workspace is bounded by the hint rather than the
potentially exponential number of table entries. -/
theorem SignedRequest.context_width_le (r : SignedRequest) :
    (ctxOf packetCallee packetSizes r.word).Wd ≤ 128 * (r.hint+1) := by
  have hl : leadOnes r.word = natBitLength r.hint := by
    unfold SignedRequest.word
    simpa only [List.append_assoc] using
      NearCubicGates.Close.CounterMachine.PrefixProg.leadOnes_natWord r.hint
        (NearCubicWires.RepairRepresentation.natWord 0 ++
          NearCubicWires.RepairRepresentation.natWord r.values.length ++ signedStream r.width r.values)
  change 2 ^ (1 * leadOnes r.word) * 64 ≤ 128 * (r.hint+1)
  rw [hl,Nat.one_mul]
  have h := NearCubicGates.Close.CounterMachine.PrefixProg.pow_nbl_le r.hint
  omega

/-- `prop:time`, paper/paper.tex:
the actual compiled signed converter is linear in table count with
only polynomial dependence on record and dimension widths. -/
theorem SignedRequest.budget_le (r : SignedRequest) :
    r.budget ≤ 10^12 * (TSK packetCallee+10) * (r.values.length+1) * (r.hint+1)^4 := by
  let H := r.hint+1
  let V := r.values.length+1
  let L := leadOnes r.word
  let W := 2^L * 64
  have hWeq : 2^L * 64 = W := rfl
  have hH : 1 ≤ H := by dsimp [H];omega
  have hV : 1 ≤ V := by dsimp [V];omega
  have hW : W ≤ 128*H := by
    have h := r.context_width_le
    simpa only [ctxOf,packetSizes,Sz.W,Nat.one_mul] using h
  have hL : L ≤ H := by
    have he : leadOnes r.word = natBitLength r.hint := by
      unfold SignedRequest.word
      simpa only [List.append_assoc] using
        NearCubicGates.Close.CounterMachine.PrefixProg.leadOnes_natWord r.hint
          (NearCubicWires.RepairRepresentation.natWord 0 ++
            NearCubicWires.RepairRepresentation.natWord r.values.length ++ signedStream r.width r.values)
    dsimp [L,H]
    rw [he]
    exact NearCubicGates.Close.WorkerArith.WorkerBounds.nbl_le_self _
  have hn : r.steps ≤ 1000*V*H := r.steps_le
  have hi : r.word.length ≤ 10*V*H := r.word_length_le
  have hw1 : W+1 ≤ 129*H := by omega
  have hlw := Nat.mul_le_mul hL hW
  have hnw := Nat.mul_le_mul hn hw1
  have hnw2 := Nat.mul_le_mul hn (Nat.pow_le_pow_left hw1 2)
  have hnt := Nat.mul_le_mul_right (TSK packetCallee+3) hn
  have hH2 : H ≤ H^2 := by nlinarith
  have hH3 : H^2 ≤ H^3 := by nlinarith
  have hH4 : H^3 ≤ H^4 := by nlinarith
  have hvh := Nat.mul_le_mul_left V (hH2.trans (hH3.trans hH4))
  have hvh2 := Nat.mul_le_mul_left V (hH3.trans hH4)
  have hvh3 := Nat.mul_le_mul_left V hH4
  have hvt := Nat.mul_le_mul_right (TSK packetCallee+3) hvh
  have hv := Nat.mul_le_mul_right (H^4) hV
  change r.budget ≤ 10^12 * (TSK packetCallee+10) * V * H^4
  unfold SignedRequest.budget langBudget
  simp only [packetSizes,Sz.W,Sz.Lk,Sz.Bk,Nat.one_mul,Nat.zero_mul,
    Nat.pow_zero,Nat.mul_zero]
  change (costA packetSizes L+1+(costB VV MM W 0 0+1+costC L W 0 0))+1+
    (r.steps*(500*(W+1)^2+100*(TSK packetCallee+3))+1+
      (10*r.word.length+5*r.steps+5*(0+3)+MM*(5*((2*W+1)*r.steps)+2)+10)) ≤ _
  simp only [costA,costB,costC,packetSizes,Sz.W,Sz.Lk,Sz.Bk,
    Nat.one_mul,Nat.zero_mul,Nat.pow_zero,Nat.mul_zero,Nat.mul_one,VV,MM]
  rw [hWeq]
  nlinarith

end NearQuarticWires.StageCertTests
