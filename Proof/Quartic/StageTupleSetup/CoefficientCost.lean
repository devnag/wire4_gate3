import Proof.Quartic.StagePrintTuple.CoefficientMachine

set_option autoImplicit false

namespace NearQuarticWires.StageTupleSetup

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Interfaces
open NearCubicGates.Close.Dispatch
open StageTuple

/-- `prop:time`, paper/paper.tex: the isolated
coefficient packet and its real executed source clock fund the actual
ordinary compiler without using any complete Terms input or size hint. -/
theorem coefficientCompiler_scalar (L N T : ℕ) (hL : L≤3*T) (hN : N≤320*T) (hT : 1≤T) :
    budgetOf VV 4 L N≤10^16*T^9 := by
  have h4 : 1≤T^4 := Nat.one_le_pow _ _ hT
  have hT9 : T≤T^9 := Nat.le_self_pow (by decide) T
  have h49 : T^4≤T^9 := Nat.pow_le_pow_right hT (by decide)
  have h59 : 1≤T^9 := Nat.one_le_pow _ _ hT
  have h5 : L+5≤8*T := by omega
  have hW : L+4≤7*T := by omega
  have hsp:=Nat.pow_le_pow_left h5 4
  have hwp:=Nat.pow_le_pow_left hW 4
  have hwd : (L+4)^4≤2401*T^4 := by nlinarith only [hwp]
  have hwc : (L+4)^4+1≤2402*T^4 := by omega
  have hkp:=Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left hwc 2)
  have hKC : KC ((L+4)^4)≤3000000000*T^8 := by
    unfold KC
    nlinarith only [hkp]
  have hsetup : setupCost VV 4 L≤211353600*T^4 := by
    unfold setupCost VV
    nlinarith only [hsp]
  have hm:=Nat.mul_le_mul hN hKC
  have hmain : N*KC ((L+4)^4)≤960000000000*T^9 := by nlinarith only [hm]
  have hs : setupCost VV 4 L≤211353600*T^9 :=
    hsetup.trans (Nat.mul_le_mul_left _ h49)
  have h30 : 30*N≤9600*T^9 := by nlinarith only [hN,hT9]
  have h50 : 50*L≤150*T^9 := by nlinarith only [hL,hT9]
  unfold budgetOf wdOf
  nlinarith only [hs,hmain,h30,h50,h59]

private theorem coefficient_bits_le (v : ℕ) : natBitLength v≤v+1 := by
  unfold natBitLength
  have hh:=Nat.log_le_self 2 v
  omega

def coefficientPacketScale (r : CoefficientRequest) : ℕ :=
  r.width+(intWord r.coefficient).length+1

theorem coefficientPacket_length (r : CoefficientRequest) :
    r.word.length≤3*coefficientPacketScale r := by
  have hb:=coefficient_bits_le r.width
  simp only [CoefficientRequest.word,List.length_append,natWord_length]
  unfold coefficientPacketScale
  omega

theorem coefficientSource_clock (r : CoefficientRequest) :
    r.steps≤320*coefficientPacketScale r := by
  have hb:=coefficient_bits_le r.width
  unfold CoefficientRequest.steps coefficientPacketScale
  omega

/-- `prop:time`, paper/paper.tex: this bounds the
SAME genuine coefficient WordFunction budget used by cold preparation.
The scale uses only its small width/signed packet, excluding Terms. -/
theorem coefficientBudget_polynomial (r : CoefficientRequest) :
    r.budget≤10^20*(r.width+(intWord r.coefficient).length+1)^9 := by
  let T:=coefficientPacketScale r
  have hT : 1≤T := by dsimp [T,coefficientPacketScale];omega
  have hL : r.word.length≤3*T := coefficientPacket_length r
  have hN : r.steps≤320*T := coefficientSource_clock r
  have hcomp : r.arithmeticBudget≤10^16*T^9 :=
    coefficientCompiler_scalar r.word.length r.steps T hL hN hT
  have h9 : T≤T^9 := Nat.le_self_pow (by decide) T
  have hp : 1≤T^9 := Nat.one_le_pow _ _ hT
  unfold CoefficientRequest.budget
  change _≤10^20*T^9
  nlinarith only [hcomp,hL,h9,hp]

end NearQuarticWires.StageTupleSetup
