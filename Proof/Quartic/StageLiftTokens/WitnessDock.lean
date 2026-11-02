import Proof.Quartic.StageCert.SourceCallGuards
import Proof.Quartic.Program.Prefix

/-!
# The retained witness and the exact digit formula

(W1)–(W3), paper/paper.tex, and `lem:print`: the physically retained, zero-padded prefix has
exactly the original proposed digit coefficients, including every
absent original witness bit.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftTokens
open NearCubicGates.Close.Interfaces StageCert.Tokens

theorem retained_witness_eq (c : Call) (p : Cells.Parameters) (w : List Bool) :
    Builder.witness c (p := p) (Program.witnessPrefix c p w)=Builder.witness c (p := p) w := by
  apply Program.decodeWitness_congr
  intro m hm
  exact Program.witnessBit_witnessPrefix c p w hm

theorem retained_chain_eq (c : Call) (p : Cells.Parameters) (w : List Bool)
    (j : Fin 2) (i : ℕ) (t : Fin (Builder.occurrences c j)) :
    Builder.chainBit c (p := p) (Program.witnessPrefix c p w) j i t=
      Builder.chainBit c (p := p) w j i t := by
  unfold Builder.chainBit
  rw [retained_witness_eq]

theorem retained_digit_weights_eq (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (j : Fin 2) (r : Fin (p.J-1+1)) :
    StagePrint.callDigitWeights c hs (Program.witnessPrefix c p w) j r=
      StagePrint.callDigitWeights c hs w j r := by
  funext t
  unfold StagePrint.callDigitWeights
  simp_rw [retained_chain_eq]

theorem retained_digit_formula_eq (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (j : Fin 2) (r : Fin (p.J-1+1)) (code : ℕ) :
    sourceDigitWalkFormula (Builder.allGates c).length r.val p.J p.k j.val
      c.first.gates.length code (Program.witnessPrefix c p w) p.factors=
      StagePrint.callWalkFormula c j (StagePrint.callDigitWeights c hs w j r)
        (StageCertTests.patternOfCode code) := by
  rw [source_digit_formula_eq_builder,retained_digit_weights_eq]

end NearQuarticWires.StageLiftTokens
