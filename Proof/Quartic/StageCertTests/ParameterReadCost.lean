import Proof.Quartic.StageCertTests.SchedulePublicBounds
import Proof.Quartic.StageLift.ParameterRun

set_option autoImplicit false

namespace NearQuarticWires.StageCertTests

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells

/-- `sec:params`, paper/paper.tex:
the literal natural-list serialization pays at least one bit per field. -/
theorem natWord_count_le_length (values : List ℕ) : values.length ≤ (values.flatMap natWord).length := by
  induction values with
  | nil => simp
  | cons value values ih =>
      simp only [List.length_cons,List.flatMap_cons,List.length_append,natWord_length]
      omega

/-- `sec:params` and `prop:time`, paper/paper.tex: all scalar reads, list-count reads and actual
counted prime/factor writes are charged by their literal source word,
with polynomial dependence only on the small field-width bound. -/
theorem parameterReadCost_le_word (p : Cells.Parameters) (B : ℕ) :
    StageLift.parameterReadCost p B ≤ 5000*((Program.parametersWord p).length+1)*(B+1) := by
  let S := (Program.parametersWord p).length
  have hbits := bitMass_le_word_length (scheduleParameterFields p)
  rw [scheduleParameterFields_word] at hbits
  simp only [scheduleParameterFields,StageLift.parameterHeadFields,StageLift.parameterTailFields,
    List.map_append,List.sum_append,List.map_cons,List.sum_cons,List.map_nil,List.sum_nil] at hbits
  have hH : ((StageLift.parameterHeadScalars p).map natBitLength).sum ≤ S := by dsimp [S];omega
  have hT : ((StageLift.parameterTailScalars p).map natBitLength).sum ≤ S := by dsimp [S];omega
  have hPB : natBitLength p.primes.card ≤ S := by dsimp [S];omega
  have hFB : natBitLength p.factors.length ≤ S := by dsimp [S];omega
  have hpc : p.primes.card ≤ ((p.primes.sort (· ≤ ·)).flatMap natWord).length := by
    have hh := natWord_count_le_length (p.primes.sort (· ≤ ·))
    rw [Finset.length_sort] at hh
    exact hh
  have hfc : p.factors.length ≤ (p.factors.flatMap natWord).length := natWord_count_le_length p.factors
  have hword := congrArg List.length (scheduleParameterFields_word p)
  simp only [scheduleParameterFields,List.flatMap_append,List.length_append] at hword
  have hpS : p.primes.card ≤ S := by dsimp [S];omega
  have hfS : p.factors.length ≤ S := by dsimp [S];omega
  have hpB := Nat.mul_le_mul_right B hpS
  have hfB := Nat.mul_le_mul_right B hfS
  change StageLift.parameterReadCost p B ≤ 5000*(S+1)*(B+1)
  unfold StageLift.parameterReadCost
  nlinarith

end NearQuarticWires.StageCertTests
