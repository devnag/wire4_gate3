import Proof.Quartic.StageCert.SourceChainDock
import Proof.Quartic.StageCert.FinalWalkForm

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicGates.Close.Interfaces

/-- `eq:testE`, paper/paper.tex: each later predecessor
is exactly the original immediately preceding retained chain bit. -/
theorem sourceDigitNegative_succ (bits : List Bool) (factors : List ℕ)
    (G row J k g : ℕ) :
    sourceDigitNegative bits factors G (row+1) J k g=
      sourceDigitPositive bits G row J k g*factors.getD row 0 := by
  simp [sourceDigitNegative,predecessorBit,sourceDigitPositive]

/-- `eq:testE` and `lem:print`, paper/paper.tex: the physically loaded signed digit coefficient at an
original occurrence is exactly its complete Builder coefficient. -/
theorem source_digit_weight_eq_builder (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (bits : List Bool)
    (j : Fin 2) (r : Fin (p.J-1+1)) (t : Fin (Builder.occurrences c j)) :
    (sourceDigitPositive bits (Builder.allGates c).length r.val p.J p.k
      (callOccurrenceOffset c j t):ℤ)-
      sourceDigitNegative bits p.factors (Builder.allGates c).length r.val p.J p.k
        (callOccurrenceOffset c j t)=StagePrint.callDigitWeights c hs bits j r t := by
  have hrJ : r.val<p.J := by have hh := r.isLt; have hp := hs.J_pos; omega
  cases hr : r.val with
  | zero =>
    simp only [hr,StagePrint.callDigitWeights,NearCubicGates.CountingCore.proposedDigit,
      sourceDigitNegative,predecessorBit,ite_true,zero_mul,Nat.cast_zero,sub_zero]
    exact (source_chain_eq_builder c p bits j 0 t).symm
  | succ i =>
    have hi : i<p.J-1 := by omega
    simp only [hr,StagePrint.callDigitWeights,NearCubicGates.CountingCore.proposedDigit,
      sourceDigitNegative_succ,Nat.cast_mul]
    rw [retainedFactor_eq_rate c hs i hi,
      ←source_chain_eq_builder c p bits j (i+1) t,←source_chain_eq_builder c p bits j i t]
    ring

/-- `eq:testPhi` and `lem:print`, paper/paper.tex: the physically loaded final coefficient retains the
entire original signed offset, including exact cancellation. -/
theorem source_final_weight_eq_builder (c : Call) (p : Cells.Parameters) (bits : List Bool)
    (j : Fin 2) (t : Fin (Builder.occurrences c j)) :
    (sourceFinalPositive bits (Builder.allGates c).length p.J p.k
      (callOccurrenceOffset c j t) p.M1:ℤ)-(p.A:ℤ)=StagePrint.callFinalWeights c p bits j t := by
  rw [sourceFinalPositive,Nat.cast_mul,←source_chain_eq_builder c p bits j (p.J-1) t]
  unfold StagePrint.callFinalWeights
  ring

end NearQuarticWires.StageCert.Tokens
