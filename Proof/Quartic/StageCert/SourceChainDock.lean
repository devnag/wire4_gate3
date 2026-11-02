import Proof.Quartic.StageCert.DigitWalkForm
import Proof.Quartic.Program.Prefix

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicGates.Close.Interfaces

/-- (W3) and `lem:print`, paper/paper.tex: the literal concatenated offset of an original circuit's
occurrence, with repeated gates retaining their separate labels. -/
def callOccurrenceOffset (c : Call) (j : Fin 2) (t : Fin (Builder.occurrences c j)) : ℕ :=
  (if j=0 then 0 else c.first.gates.length)+t.val

/-- (W3) and `lem:print`, paper/paper.tex: the physical retained-chain bit at its original global
address is exactly the Builder coefficient, including absent-row zeros.
The statement holds for every witness, before any certification. -/
theorem source_chain_eq_builder (c : Call) (p : Cells.Parameters) (bits : List Bool)
    (j : Fin 2) (row : ℕ) (t : Fin (Builder.occurrences c j)) :
    Builder.chainBit c (p := p) bits j row t=
      (sourceDigitPositive bits (Builder.allGates c).length row p.J p.k
        (callOccurrenceOffset c j t):ℤ) := by
  by_cases hrow : row<p.J
  · rw [sourceDigitPositive,if_pos hrow,Builder.chainBit,dif_pos hrow]
    have hindex : p.k+(Builder.occurrences c 0+Builder.occurrences c 1)+
        row*(Builder.occurrences c 0+Builder.occurrences c 1)+
        (if j=0 then 0 else Builder.occurrences c 0)+t.val=
        (row+1)*(Builder.allGates c).length+p.k+callOccurrenceOffset c j t := by
      simp only [Builder.occurrences,Builder.gatesOf,Matrix.cons_val_zero,Matrix.cons_val_one,
        Matrix.cons_val_fin_one,Builder.allGates,List.length_append,callOccurrenceOffset]
      ring
    change Algorithm.CellCall.bitInt (bits.getD
      (p.k+(Builder.occurrences c 0+Builder.occurrences c 1)+
        row*(Builder.occurrences c 0+Builder.occurrences c 1)+
        (if j=0 then 0 else Builder.occurrences c 0)+t.val) false)=_
    rw [hindex]
    cases bits.getD ((row+1)*(Builder.allGates c).length+p.k+callOccurrenceOffset c j t) false <;> rfl
  · simp only [Builder.chainBit,dif_neg hrow,sourceDigitPositive,if_neg hrow,Nat.cast_zero]

end NearQuarticWires.StageCert.Tokens
