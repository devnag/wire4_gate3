import Proof.Quartic.StagePrintTuple.Request
import Proof.Quartic.StagePrintTuple.ChildCounter

set_option autoImplicit false

namespace NearQuarticWires.StageTuple

open NearCubicGates.Close.Tabulator
open NearCubicWires (natBitLength)

/-- `lem:print` and `prop:time`, paper/paper.tex: the distinct actual monomial list has the ordinary
bounded-support count, independently of its child-choice census. -/
theorem terms_count_le {V : ℕ} (terms : Terms V) (D : ℕ)
    (hn : (Terms.keys terms).Nodup) (hD : ∀S∈Terms.keys terms,S.card≤D) :
    terms.length≤(1+V)^D := by
  have h := weighted_support_sum_le V D 1 (Terms.keys terms).toFinset (by
    intro S hS
    exact hD S (List.mem_toFinset.mp hS))
  have hc : (Terms.keys terms).toFinset.card=terms.length := by
    rw [List.toFinset_card_of_nodup hn]
    simp [Terms.keys]
  simpa [hc] using h

/-- `prop:time`, paper/paper.tex: the one-time
numeric Terms-count parser is an additive squared-support stage. Its
square stays inside the same sharp degree-2D native census. -/
theorem TermCutRequest.termCount_sq_le (r : TermCutRequest) (mc : ℕ) (hmc : 1≤ mc) :
    r.terms.length^2≤(1+17*(Builder.allGates r.header.call).length*mc)^(2*r.degree) := by
  have hn := terms_count_le r.terms r.degree r.terms_nodup r.terms_degree
  have hs := Nat.pow_le_pow_left hn 2
  rw [←pow_mul] at hs
  have hb : 1+17*(Builder.allGates r.header.call).length≤
      1+17*(Builder.allGates r.header.call).length*mc := by nlinarith
  exact hs.trans (by rw [Nat.mul_comm r.degree 2];exact Nat.pow_le_pow_left hb _)

/-- `prop:time`, paper/paper.tex: the real
binary count decoder's bounded unary-register clock is quadratic only
in that one physically parsed count, before all per-monomial work. -/
theorem natural_count_readCost_le (j : ℕ) :
    (natBitLength j+2)*(40*2^(natBitLength j)+40)≤1000*(j+1)^2 := by
  have hb := childCount_bits j
  have hp : 2^(natBitLength j)≤2*(j+1) := by
    unfold natBitLength
    rw [pow_succ]
    have hh:=Nat.pow_log_le_add_one 2 j
    nlinarith
  nlinarith

end NearQuarticWires.StageTuple
