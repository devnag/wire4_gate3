import Proof.Quartic.StageCert.MomentBounds
import Proof.Quartic.Cells.ParametersCertificateBits

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open Finset
open NearQuarticWires
open NearCubicWires
open NearCubicGates.Close.Interfaces

variable (c : Call) {p : Cells.Parameters} (hs : Cells.ParameterRules (Builder.callInput c) p)

/-- `sec:walks`, paper/paper.tex: every signed contribution
of a single raw occurrence has absolute value at most eight. -/
theorem contribution_abs_le (bits : List Bool) (z : Fin (2^(c.n-p.k))) (j : Fin 2)
    (t : Fin (Builder.occurrences c j)) (σ : Cycle.SignPattern 4)
    (w : Cycle.Walk hs.seedParameters.N 4) :
    |Builder.contribution c hs bits z j t σ w| ≤ 8 := by
  unfold Builder.contribution
  calc
    |∑ l, _| ≤ ∑ l, |Cycle.signValue (σ l)*_| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _l : Fin 8, (1 : ℤ) := by
      apply Finset.sum_le_sum
      intro l _
      rw [abs_mul,Cycle.abs_signValue,one_mul]
      exact Cells.delta_abs_le _ _ _ _ _
    _ = _ := by norm_num

/-- `sec:algorithm`, paper/paper.tex: every proposed
sampling coefficient is an integer zero or one, for every witness word. -/
theorem chainBit_abs_le (bits : List Bool) (j : Fin 2) (i : ℕ)
    (t : Fin (Builder.occurrences c j)) : |Builder.chainBit c (p := p) bits j i t| ≤ 1 := by
  unfold Builder.chainBit Algorithm.CellCall.bitInt
  split_ifs <;> norm_num

/-- `sec:walks`, paper/paper.tex: arbitrary proposed chain
values remain bounded by the occurrence count; no sampling premise is used. -/
theorem column_values_abs_le (bits : List Bool) (z : Fin (2^(c.n-p.k))) (j : Fin 2)
    (σ : Cycle.SignPattern 4) (w : Cycle.Walk hs.seedParameters.N 4) (i : ℕ) :
    |(Builder.columnData c hs bits z).values j σ w i| ≤ 8*(Builder.occurrences c j : ℤ) := by
  change |∑ t : Fin (Builder.occurrences c j),
    Builder.chainBit c (p := p) bits j i t * Builder.contribution c hs bits z j t σ w| ≤ _
  calc
    |∑ t, _| ≤ ∑ t, |Builder.chainBit c (p := p) bits j i t * Builder.contribution c hs bits z j t σ w| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t : Fin (Builder.occurrences c j), (8 : ℤ) := by
      apply Finset.sum_le_sum
      intro t _
      rw [abs_mul]
      calc
        _ ≤ 1*8 := mul_le_mul (chainBit_abs_le c bits j i t)
          (contribution_abs_le c hs bits z j t σ w) (abs_nonneg _) (by norm_num)
        _ = _ := by norm_num
    _ = _ := by simp [mul_comm]

/-- `def:mask`, paper/paper.tex: the witness-selected
population is at most the total original occurrence count on every point. -/
theorem column_X_le (bits : List Bool) (z : Fin (2^(c.n-p.k)))
    (q : Sampler.Cell hs.seedParameters.N) :
    (Builder.columnData c hs bits z).X q ≤ Builder.occurrences c 0+Builder.occurrences c 1 := by
  change (∑ i : Fin (Builder.allGates c).length, _) ≤ _
  calc
    _ ≤ ∑ _i : Fin (Builder.allGates c).length, 1 := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs
      · have h := Cells.delta_abs_le (Builder.star c hs)
          ((Builder.allGates c)[(i:ℕ)]'i.isLt) (Builder.center c hs bits z)
          (Builder.pattern c hs q.1) (Builder.pattern c hs q.2)
        have h' : ((Cells.delta (Builder.star c hs)
            ((Builder.allGates c)[(i:ℕ)]'i.isLt) (Builder.center c hs bits z)
            (Builder.pattern c hs q.1) (Builder.pattern c hs q.2)).natAbs : ℤ) ≤ 1 := by
          simpa only [Int.natCast_natAbs] using h
        exact_mod_cast h' 
      · omega
    _ = _ := by simp [Builder.allGates,Builder.occurrences,Builder.gatesOf]

end NearQuarticWires.StageCert

namespace NearQuarticWires.StageCert
open Finset
open NearQuarticWires
open NearCubicWires
open NearCubicGates.Close.Interfaces

/-- `sec:walks`, paper/paper.tex: a proposed digit has a
uniform range for arbitrary integer values and rate multipliers. -/
theorem proposedDigit_abs_le (B R : ℕ) (rate value : ℕ → ℤ)
    (hr : ∀ i, |rate i| ≤ R) (hv : ∀ i, |value i| ≤ B) (i : ℕ) :
    |NearCubicGates.CountingCore.proposedDigit rate value i| ≤ (B : ℤ)*(R+1) := by
  cases i with
  | zero =>
    change |value 0| ≤ _
    have h := hv 0
    nlinarith
  | succ i =>
    change |value (i+1)-rate i*value i| ≤ _
    calc
      _ ≤ |value (i+1)|+|rate i*value i| := by
        simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (value (i+1)) (-(rate i*value i))
      _ ≤ (B : ℤ)+(R : ℤ)*B := by
        rw [abs_mul]
        exact add_le_add (hv _) (mul_le_mul (hr _) (hv _) (abs_nonneg _) (Int.natCast_nonneg _))
      _ = _ := by ring

/-- `sec:params`, paper/paper.tex: every rate in the
actual selected column data is bounded by the input arity. -/
theorem column_rate_abs_le (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (bits : List Bool)
    (z : Fin (2^(c.n-p.k))) (i : ℕ) : |(Builder.columnData c hs bits z).rate i| ≤ c.n := by
  change |((NearCubicGates.RationalRateChain.factorRat
    (NearCubicGates.RationalRateChain.ratio
      (NearCubicGates.Close.Counter.firstRatio p.ell0 p.h p.T) i) : ℕ) : ℤ)| ≤ _
  rw [abs_of_nonneg (Int.natCast_nonneg _)]
  exact_mod_cast hs.chain_factor_le_n i

/-- `eq:testE`, paper/paper.tex: every actual proposed digit has
an unconditional range, including malformed or unsampled witness chains. -/
theorem column_digit_abs_le (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (bits : List Bool)
    (z : Fin (2^(c.n-p.k))) (j : Fin 2) (σ : Cycle.SignPattern 4)
    (w : Cycle.Walk hs.seedParameters.N 4) (i : Fin (p.J-1+1)) :
    |(Builder.columnData c hs bits z).E j σ w i| ≤
      (8*(Builder.occurrences c j) : ℕ)*((c.n : ℤ)+1) := by
  apply proposedDigit_abs_le (8*Builder.occurrences c j) c.n
    (Builder.columnData c hs bits z).rate ((Builder.columnData c hs bits z).values j σ w)
    (column_rate_abs_le c hs bits z)
  intro t
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using column_values_abs_le c hs bits z j σ w t

/-- `eq:testPhi`, paper/paper.tex: the complete final-error
range holds for every proposed chain and every original column. -/
theorem column_phi_abs_le (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (bits : List Bool)
    (z : Fin (2^(c.n-p.k))) (j : Fin 2) (σ : Cycle.SignPattern 4)
    (w : Cycle.Walk hs.seedParameters.N 4) :
    |(Builder.columnData c hs bits z).phi (by norm_num) j σ w| ≤
      (8*(Builder.occurrences c j) : ℕ)*((p.M1 : ℤ)+p.A) := by
  have hv := column_values_abs_le c hs bits z j σ w (p.J-1)
  have hy : |(Builder.columnData c hs bits z).Y (by norm_num) j σ w| ≤
      8*(Builder.occurrences c j : ℤ) := by
    apply Cycle.abs_walkSum_le (by norm_num) _ (Builder.occurrences c j)
    intro q
    exact Cells.residual_abs_le _ _ _ _ _
  change |(p.M1 : ℤ)*_-(p.A : ℤ)*_| ≤ _
  calc
    _ ≤ |(p.M1 : ℤ)*_|+|(p.A : ℤ)*_| := by
      simpa only [sub_eq_add_neg,abs_neg] using abs_add_le
        ((p.M1:ℤ)*(Builder.columnData c hs bits z).values j σ w (p.J-1))
        (-((p.A:ℤ)*(Builder.columnData c hs bits z).Y (by norm_num) j σ w))
    _ ≤ (p.M1 : ℤ)*(8*(Builder.occurrences c j : ℤ))+
        (p.A : ℤ)*(8*(Builder.occurrences c j : ℤ)) := by
      simp only [abs_mul,abs_of_nonneg (Int.natCast_nonneg _)]
      exact add_le_add (mul_le_mul_of_nonneg_left hv (Int.natCast_nonneg _))
        (mul_le_mul_of_nonneg_left hy (Int.natCast_nonneg _))
    _ = _ := by push_cast; ring

end NearQuarticWires.StageCert
