import Proof.Quartic.StagePrint.RawInitialization

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.RawBits
open NearCubicWires
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Dispatch (lt_natBitLength)
open NearCubicGates.Close.Interfaces (intWord listWord)
open NearCubicGates.Close.WordPrograms.SInt (encS)

/-- `lem:print`, paper/paper.tex: the cold source record contains the chosen field width and the original dense gate word. -/
def originalGateSource (r : OriginalChildRequest) : List Bool :=
  natWord (r.W+1)++listWord intWord r.weights++intWord (r.target+1)

/-- `lem:print`, paper/paper.tex: every original integer occurrence has its own explicitly bounded source span. -/
theorem intWord_member_length (zs : List ℤ) (z : ℤ) (hz : z∈zs) :
    (intWord z).length≤(zs.flatMap intWord).length := by
  induction zs with
  | nil => simp at hz
  | cons v zs ih =>
    rcases List.mem_cons.mp hz with h|h
    · subst z;simp only [List.flatMap_cons,List.length_append];omega
    · exact (ih h).trans (by simp)

/-- `lem:print`, paper/paper.tex: no zero coefficient occurrence is omitted from the dense source census. -/
theorem dense_count_le_word (zs : List ℤ) :
    zs.length≤(zs.flatMap intWord).length := by
  induction zs with
  | nil => simp
  | cons z zs ih =>
    have hpos : 1≤(intWord z).length := by
      unfold intWord
      simp only [List.length_append,NearCubicGates.Close.Dispatch.natWord_length]
      omega
    simp only [List.length_cons,List.flatMap_cons,List.length_append]
    omega

/-- `lem:print`, paper/paper.tex: signed arithmetic is bounded by the actual canonical input span, independently of coefficient values. -/
theorem signed_code_word_bound (z : ℤ) (L : ℕ) (hz : (intWord z).length≤L) :
    encS z+3<2^(L+3) := by
  have hn : natBitLength z.natAbs≤L := by
    have hh:=NearCubicGates.Close.Dispatch.natBitLength_le_len z.natAbs
    have hs : (natWord z.natAbs).length≤(intWord z).length := by
      unfold intWord; simp
    omega
  have ha : z.natAbs<2^L := lt_of_lt_of_le (lt_natBitLength z.natAbs)
    (Nat.pow_le_pow_right (by decide) hn)
  have hp : 1≤2^L:=Nat.one_le_two_pow
  rw [show L+3=L+1+1+1 by omega,pow_succ,pow_succ,pow_succ]
  unfold encS
  split_ifs <;> omega

/-- `lem:print`, paper/paper.tex: every numeric field needed by the cold formatter fits one workspace determined by its actual source word. -/
theorem originalGateSource_bounds (r : OriginalChildRequest) :
    natBitLength (r.W+1)≤(originalGateSource r).length ∧
    r.weights.length≤(originalGateSource r).length ∧
    (∀z∈r.weights,(intWord z).length≤(originalGateSource r).length) ∧
    (intWord (r.target+1)).length≤(originalGateSource r).length := by
  have hn:=NearCubicGates.Close.Dispatch.natBitLength_le_len (r.W+1)
  have hc:=dense_count_le_word r.weights
  have hh : (r.weights.flatMap intWord).length≤(listWord intWord r.weights).length := by
    unfold listWord;simp
  simp only [originalGateSource,List.length_append]
  refine ⟨by omega,by omega,?_,by omega⟩
  intro z hz
  have hm:=intWord_member_length r.weights z hz
  omega

end NearQuarticWires.StagePrint.RawBits
