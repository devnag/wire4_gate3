import Proof.Quartic.StageCertNative.PoolCostTarget
import Proof.Quartic.Cells.ParametersRecoveryReserve

set_option autoImplicit false

namespace NearQuarticWires.StageCertNativePoolCost

open NearCubicWires
open StageCertNative StageCertificateControl

/-- `eq:testX`–`eq:testPhi`, paper/paper.tex:
all original terms share the exact full moment degree. -/
noncomputable def wholeDegree {B1 B2 : ℕ} (r : IndexedRequest B1 B2) : ℕ :=
  16*r.prepared.selected.1.Xmax+8*r.prepared.selected.1.k

theorem term_degree_eq {B1 B2 : ℕ} (r : IndexedRequest B1 B2) (i : Fin (termCount r)) :
    (actualMoment r i).packet.degree=wholeDegree r := rfl

/-- `prop:time`, paper/paper.tex: the
actual population or closed-walk count is bounded without replacing
the population loop by a padded census. -/
theorem termCount_power_bound {B1 B2 : ℕ} (r : IndexedRequest B1 B2) :
    termCount r≤2^(4*r.prepared.selected.1.k) := by
  have hs:=Cells.prepare_spec _ r.prepared.selected.1 r.prepared.selected.2
  have hh:=termCount_le_eighth r
  rw [hs.N_eq,←pow_mul] at hh
  exact hh.trans (Nat.pow_le_pow_right (by decide) (by omega))

theorem count_square_binary {B1 B2 : ℕ} (r : IndexedRequest B1 B2) :
    (termCount r)^2≤2^(8*r.prepared.selected.1.k) := by
  have hh:=Nat.pow_le_pow_left (termCount_power_bound r) 2
  rw [←pow_mul] at hh
  have he : 4*r.prepared.selected.1.k*2=8*r.prepared.selected.1.k := by omega
  rw [he] at hh
  exact hh

/-- `prop:time`, paper/paper.tex: two
term-count powers are absorbed by one actual moment-degree power
of the unchanged selected occurrence census. -/
theorem count_square_degree {B1 B2 : ℕ} (r : IndexedRequest B1 B2) :
    (termCount r)^2≤r.prepared.selected.1.Uocc^wholeDegree r := by
  have hs:=Cells.prepare_spec _ r.prepared.selected.1 r.prepared.selected.2
  calc
    _≤2^(8*r.prepared.selected.1.k) := count_square_binary r
    _≤2^wholeDegree r := Nat.pow_le_pow_right (by decide) (by unfold wholeDegree;omega)
    _≤_ := Nat.pow_le_pow_left hs.Uocc_two _

/-- `prop:time`, paper/paper.tex: the
legacy numeric index-squared writer and conservative sum-times-count
loop are paid by the genuine fourth power, not a quadratic proxy. -/
theorem count_fourth_bound {B1 B2 : ℕ} (r : IndexedRequest B1 B2) :
    (termCount r)^4≤2^(8*r.prepared.selected.1.k)*r.prepared.selected.1.Uocc^wholeDegree r := by
  have hh:=Nat.mul_le_mul (count_square_binary r) (count_square_degree r)
  simpa only [←pow_add] using hh

/-- `sec:params` and `prop:time`, paper/paper.tex: the unchanged original 50D reserve
pays the complete whole-test compiler budget. -/
theorem whole_reserve {B1 B2 : ℕ} (r : IndexedRequest B1 B2) :
    2^(8*r.prepared.selected.1.k)*r.prepared.selected.1.Uocc^(50*wholeDegree r)≤
      2^(r.prepared.call.n-r.prepared.selected.1.k) := by
  have hs:=Cells.prepare_spec _ r.prepared.selected.1 r.prepared.selected.2
  have hD : wholeDegree r≤r.prepared.selected.1.Dmax := by
    have hh:=hs.moment_degree
    rw [hs.m_eq] at hh
    exact hh
  have hU:=hs.Uocc_two
  have he : r.prepared.selected.1.Uocc-1+1=r.prepared.selected.1.Uocc := by omega
  have hh:=hs.recovery_compiler_reserve (r.prepared.selected.1.Uocc-1) (wholeDegree r)
    (by omega) hD
  rw [he] at hh
  exact hh

theorem count_fourth_reserve {B1 B2 : ℕ} (r : IndexedRequest B1 B2) :
    (termCount r)^4≤2^(r.prepared.call.n-r.prepared.selected.1.k) := by
  have hs:=Cells.prepare_spec _ r.prepared.selected.1 r.prepared.selected.2
  exact (count_fourth_bound r).trans ((Nat.mul_le_mul_left _
    (Nat.pow_le_pow_right (by have hh:=hs.Uocc_two;omega) (by omega))).trans (whole_reserve r))

/-- `prop:time`, paper/paper.tex: the
actual per-term occurrence exponent four is summed and multiplied
by the original loop count under the same untouched reserve. -/
theorem count_squared_price_reserve {B1 B2 : ℕ} (r : IndexedRequest B1 B2) :
    (termCount r)^2*r.prepared.selected.1.Uocc^(4*wholeDegree r)≤
      2^(r.prepared.call.n-r.prepared.selected.1.k) := by
  have hs:=Cells.prepare_spec _ r.prepared.selected.1 r.prepared.selected.2
  calc
    _≤r.prepared.selected.1.Uocc^wholeDegree r*r.prepared.selected.1.Uocc^(4*wholeDegree r) :=
      Nat.mul_le_mul_right _ (count_square_degree r)
    _=r.prepared.selected.1.Uocc^(5*wholeDegree r) := by rw [←pow_add];congr 1;omega
    _≤r.prepared.selected.1.Uocc^(50*wholeDegree r) :=
      Nat.pow_le_pow_right (by have hh:=hs.Uocc_two;omega) (by omega)
    _≤2^(8*r.prepared.selected.1.k)*r.prepared.selected.1.Uocc^(50*wholeDegree r) :=
      Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
    _≤_ := whole_reserve r

end NearQuarticWires.StageCertNativePoolCost
