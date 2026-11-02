import Proof.Quartic.StageCert.SourceFormulaDock
import Proof.Quartic.Cells.ParametersCertWeights

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicGates.Close.Interfaces

/-- Step 1 and `lem:print`, paper/paper.tex: every actually dispatched certificate call has a nonempty
original occurrence pool; zero-wire calls have already been answered. -/
theorem dispatched_originalPool_pos {B1 B2 : ℕ} {c : Call} {p : Program.Selected c}
    (hd : Program.dispatch B1 B2 c=some p) : 0<(Builder.allGates c).length := by
  have hwire := (Program.dispatch_admitted hd).2
  by_contra h
  have hz : (Builder.allGates c).length=0 := by omega
  have hboth : c.first.gates.length=0 ∧ c.second.gates.length=0 := by
    simpa only [Builder.allGates,List.length_append,Nat.add_eq_zero_iff] using hz
  have hfirst := List.length_eq_zero_iff.mp hboth.1
  have hsecond := List.length_eq_zero_iff.mp hboth.2
  apply hwire
  simp only [Transfer.callWires,Transfer.wires,hfirst,hsecond,List.map_nil,List.sum_nil,Nat.add_zero]

/-- (W1)–(W3), `sec:algorithm`, paper/paper.tex: the actual retained
source prefix has the complete selected and proposed-chain horizon,
including physical false padding for a short original witness. -/
theorem source_witness_prefix_length (c : Call) (p : Cells.Parameters) (w : List Bool) :
    (Program.witnessPrefix c p w).length=p.k+(p.J+1)*(Builder.allGates c).length := by
  simp [Program.witnessPrefix,Program.witnessReadLength,Builder.allGates,Builder.occurrences,Builder.gatesOf]

/-- `imp:chain` and `eq:testE`, paper/paper.tex: every physically requested digit rate has an arity bound
before certification, including the first row's literal unit rate. -/
theorem source_digit_rate_le (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (r : Fin (p.J-1+1)) :
    (if r.val=0 then 1 else p.factors.getD (r.val-1) 0)≤c.n+1 := by
  by_cases hr : r.val=0
  · simp only [if_pos hr]
    omega
  · have hi : r.val-1<p.J-1 := by have hh := r.isLt; omega
    rw [if_neg hr,retainedFactor_eq_rate c hs _ hi]
    exact (hs.chain_factor_le_n _).trans (Nat.le_succ c.n)

/-- `eq:testE` and `lem:print`, paper/paper.tex: the emitted original global digit coefficient has the
selected arity bound for every witness, without assuming any test passed. -/
theorem source_digit_global_natAbs_le (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (bits : List Bool)
    (j : Fin 2) (r : Fin (p.J-1+1)) (g : Fin (Builder.allGates c).length) :
    (sourceDigitGlobalWeights c p bits j r.val g).natAbs≤1+c.n := by
  rw [source_digit_global_eq_builder]
  exact Cells.ParameterArithmetic.circuit_weights_natAbs_le c j
    (StagePrint.callDigitWeights c hs bits j r) (1+c.n)
    (Cells.ParameterArithmetic.call_digit_weights_natAbs_le c hs bits j r) g

/-- `eq:testPhi` and `lem:print`, paper/paper.tex: complete original final-error coefficients have
the selected scale bound on every proposed witness and every column. -/
theorem source_final_global_natAbs_le (c : Call) (p : Cells.Parameters) (bits : List Bool)
    (j : Fin 2) (g : Fin (Builder.allGates c).length) :
    (sourceFinalGlobalWeights c p bits j g).natAbs≤p.M1+p.A := by
  rw [source_final_global_eq_builder]
  exact Cells.ParameterArithmetic.circuit_weights_natAbs_le c j
    (StagePrint.callFinalWeights c p bits j) (p.M1+p.A)
    (Cells.ParameterArithmetic.call_final_weights_natAbs_le c p bits j) g

end NearQuarticWires.StageCert.Tokens
