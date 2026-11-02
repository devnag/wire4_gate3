import Proof.Quartic.StageCert.MomentBudgetBound
import Proof.Quartic.StageCert.MomentRuntimeArity
import Proof.Quartic.Cells.ParametersRecoveryReserve

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires
open NearCubicGates.Close.Cells

/-- `prop:time`, paper/paper.tex: the actual
cold expression source has one fixed arity coefficient and exponent;
the tuple-enumeration factor remains explicit. -/
noncomputable def momentSourcePriceCoefficient (B1 B2 : ℕ) : ℕ :=
  100000000000000*(momentRuntimeCoefficient B1 B2)^5

noncomputable def momentSourcePriceExponent (B1 B2 : ℕ) : ℕ :=
  5*momentRuntimeExponent B1 B2

private theorem source_price_rearrange (M C b E : ℕ) :
    100000000000000*M*(C*b^E)^5=
      (100000000000000*C^5)*b^(5*E)*M := by
  rw [mul_pow,←pow_mul]
  rw [Nat.mul_comm E 5]
  ring

/-- `lem:print` and `prop:time`, paper/paper.tex: the full physical source clock includes every binary
operation while retaining the exact guarded tuple factor. -/
theorem MomentRequest.sourceBudget_arity {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    r.sourceBudget ≤ momentSourcePriceCoefficient B1 B2*
      (r.call.n+1)^momentSourcePriceExponent B1 B2*
      (Builder.allGates r.call).length^r.selected.1.Xmax := by
  have hp := Nat.pow_le_pow_left r.runtimeScale_arity 5
  calc
    r.sourceBudget ≤ 100000000000000*(Builder.allGates r.call).length^r.selected.1.Xmax*
        r.runtimeScale^5 := r.sourceBudget_le
    _ ≤ 100000000000000*(Builder.allGates r.call).length^r.selected.1.Xmax*
        (momentRuntimeCoefficient B1 B2*(r.call.n+1)^momentRuntimeExponent B1 B2)^5 :=
      Nat.mul_le_mul_left _ hp
    _ = _ := source_price_rearrange _ _ _ _

/-- `sec:params` and `lem:print`, paper/paper.tex: the actual seventeen-role source pool, with both
literal expansion constants, fits the selected occurrence census. -/
theorem MomentRequest.source_occurrence_guard {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    17*(Builder.allGates r.call).length+2 ≤ r.selected.1.Uocc := by
  let hs := r.rules
  have hG : (Builder.allGates r.call).length ≤ 2*r.call.n^4 := by
    have hh := hs.input_valid.2.2.1.trans hs.input_valid.2.2.2.1
    simpa only [Builder.callInput,Builder.allGates,List.length_append] using hh
  have hn : 1 ≤ r.call.n := by
    have hh := hs.input_valid.1
    change 4≤r.call.n at hh
    omega
  have hc : 2 ≤ r.selected.1.childCap := by
    rw [hs.childCap_eq]
    change 2≤r.call.n*(NearCubicGates.Close.Counter.B0 r.call.n+Nat.clog 2 r.call.n+3)
    nlinarith
  have ha : 17*(Builder.allGates r.call).length ≤ r.selected.1.NatAtoms := by
    rw [hs.NatAtoms_eq,hs.m_eq]
    change 17*(Builder.allGates r.call).length≤17*(2*r.call.n^4)
    exact Nat.mul_le_mul_left 17 hG
  have hp := Nat.mul_le_mul_left r.selected.1.NatAtoms hc
  have hpos := r.pool_pos
  rw [hs.Uocc_eq]
  nlinarith only [ha,hp,hpos]

/-- `eq:testE`–`eq:testPhi` and `sec:params`, paper/paper.tex: the source's literal full-moment
degree is the exact selected degree guard, without a passing-test premise. -/
theorem MomentRequest.source_degree_guard {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    16*r.selected.1.Xmax+8*r.selected.1.k ≤ r.selected.1.Dmax := by
  have hh := r.rules.moment_degree
  rw [r.rules.m_eq] at hh
  exact hh

/-- `lem:print` and `prop:time`, paper/paper.tex: all guarded tuple bodies over the exact closed-walk
census fit the unchanged original degree reserve. -/
theorem MomentRequest.source_tuple_reserve {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    2^(4*r.selected.1.k)*(Builder.allGates r.call).length^r.selected.1.Xmax ≤
      2^(r.call.n-r.selected.1.k) := by
  let G := (Builder.allGates r.call).length
  let D := 16*r.selected.1.Xmax+8*r.selected.1.k
  have hV : G+1≤r.selected.1.Uocc := by
    have hh := r.source_occurrence_guard
    dsimp only [G]
    omega
  have hp : G^r.selected.1.Xmax≤(G+1)^(3*D) :=
    (Nat.pow_le_pow_left (Nat.le_succ G) _).trans
      (Nat.pow_le_pow_right (Nat.succ_pos G) (by dsimp only [D]; omega))
  exact (Nat.mul_le_mul_left _ hp).trans
    (r.rules.recovery_all_walks_reserve G D hV r.source_degree_guard)

/-- `prop:time`, paper/paper.tex: construction
of every exact signed per-walk expression is charged to one fixed
polynomial times the number of original outer columns. -/
theorem MomentRequest.sourceBudget_all_walks {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    2^(4*r.selected.1.k)*r.sourceBudget ≤
      momentSourcePriceCoefficient B1 B2*(r.call.n+1)^momentSourcePriceExponent B1 B2*
        2^(r.call.n-r.selected.1.k) := by
  calc
    _ ≤ 2^(4*r.selected.1.k)*(momentSourcePriceCoefficient B1 B2*
        (r.call.n+1)^momentSourcePriceExponent B1 B2*
        (Builder.allGates r.call).length^r.selected.1.Xmax) :=
      Nat.mul_le_mul_left _ r.sourceBudget_arity
    _ = (momentSourcePriceCoefficient B1 B2*(r.call.n+1)^momentSourcePriceExponent B1 B2)*
        (2^(4*r.selected.1.k)*(Builder.allGates r.call).length^r.selected.1.Xmax) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ r.source_tuple_reserve

end NearQuarticWires.StageCert.Tokens
