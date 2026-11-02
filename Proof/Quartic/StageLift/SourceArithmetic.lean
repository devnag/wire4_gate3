import Proof.Quartic.StageLift.SourceWidth
import Proof.Quartic.StageRecovery.ResidueFactor

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

/-- `prop:time`, paper/paper.tex: the common
quadratic binary workspace contains every fixed quartic source
intermediate, without depending on a large input suffix. -/
theorem source_polynomial_fits (E W : ℕ) (hW : 100 * (E + 1) ^ 2 ≤ W) :
    100 * (E + 1) ^ 4 < 2 ^ W := by
  have hT : 1 ≤ E + 1 := by omega
  have hpower := Nat.pow_le_pow_left (Nat.lt_two_pow_self (n := E + 1)).le 4
  rw [← pow_mul] at hpower
  have hp : 0 < (2 : ℕ) ^ ((E + 1) * 4) := Nat.pow_pos (by decide)
  have hsmall : 100 * (E + 1) ^ 4 < 128 * 2 ^ ((E + 1) * 4) := by omega
  have hsq : E + 1 ≤ (E + 1) ^ 2 := Nat.le_self_pow (by decide) _
  have hexp : (E + 1) * 4 + 7 ≤ W := by nlinarith only [hW, hsq]
  calc
    _ < 128 * 2 ^ ((E + 1) * 4) := hsmall
    _ = 2 ^ ((E + 1) * 4 + 7) := by rw [pow_add]; norm_num; ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) hexp

/-- `sec:params` and `lem:print`, paper/paper.tex: every intermediate of the literal degree computation
fits the selected arithmetic workspace on every actual print request. -/
theorem source_degree_room {B1 B2 : ℕ} (C : Ctx) (r : Greedy.PrintRequest B1 B2)
    (hW : 100 * (sourceEnvelope r + 1) ^ 2 ≤ C.Wd) :
    16 * r.child.selected.1.Xmax +
      (2 * r.child.selected.1.e - 1) * (2 * (r.child.selected.1.J + 1)) * r.prime +
      2 * r.child.selected.1.e + 2 * (r.child.selected.1.J + 1) + r.prime + 17 < 2 ^ C.Wd := by
  let E := sourceEnvelope r
  have hs := Cells.prepare_spec _ r.child.selected.1 r.child.selected.2
  have hadm := (Program.dispatch_admitted r.child.dispatched).1
  have hb : 1 ≤ r.child.call.radius * (r.child.call.n : ℚ) ^ B1 :=
    hadm.2.2.2.2.2.2.2.2.2.1
  have hx0 : r.child.selected.1.Xmax ≤ Cells.ParameterArithmetic.preparationEnvelope B1 r.child.call.n :=
    (hs.scalar_preparation_bounds B1 hb).Xmax
  have hx : r.child.selected.1.Xmax ≤ E :=
    hx0.trans (by dsimp [E, sourceEnvelope]; omega)
  have hbds := sourceEnvelope_bounds r
  have he : r.child.selected.1.e ≤ E := hbds.exponent
  have hJ : r.child.selected.1.J ≤ E := hbds.chains
  have hp : r.prime ≤ E := hbds.prime
  have hprod := Nat.mul_le_mul
    (Nat.mul_le_mul (show 2 * r.child.selected.1.e - 1 ≤ 2 * (E + 1) by omega)
      (show 2 * (r.child.selected.1.J + 1) ≤ 2 * (E + 1) by omega))
    (hp.trans (Nat.le_succ _))
  have hbase : 1 ≤ E + 1 := by omega
  have h34 : (E + 1) ^ 3 ≤ (E + 1) ^ 4 := Nat.pow_le_pow_right hbase (by decide)
  have h14 : E + 1 ≤ (E + 1) ^ 4 := Nat.le_self_pow (by decide) _
  have hbound : 16 * r.child.selected.1.Xmax +
      (2 * r.child.selected.1.e - 1) * (2 * (r.child.selected.1.J + 1)) * r.prime +
      2 * r.child.selected.1.e + 2 * (r.child.selected.1.J + 1) + r.prime + 17 ≤
      100 * (E + 1) ^ 4 := by nlinarith only [hx, he, hJ, hp, hprod, h34, h14]
  exact hbound.trans_lt (source_polynomial_fits E C.Wd hW)

/-- `lem:residue` and `prop:time`, paper/paper.tex: streaming reductions use the actual modulus within
source width, before any multiplication by the raw index magnitude. -/
theorem source_modulus_fits {B1 B2 : ℕ} (C : Ctx) (r : Greedy.PrintRequest B1 B2)
    (hW : 100 * (sourceEnvelope r + 1) ^ 2 ≤ C.Wd) :
    2 * r.prime ^ r.child.selected.1.e ≤ 2 ^ C.Wd := by
  let E := sourceEnvelope r
  have hb := sourceEnvelope_bounds r
  have hn := StageRecovery.primePower_bits_envelope r.prime r.child.selected.1.e E hb.prime hb.exponent
  have hq := lt_natBitLength (r.prime ^ r.child.selected.1.e)
  have hpow : r.prime ^ r.child.selected.1.e < 2 ^ ((E + 1) ^ 2) :=
    hq.trans_le (Nat.pow_le_pow_right (by decide) hn)
  have hp := Nat.mul_lt_mul_of_pos_left hpow (show 0 < 2 by decide)
  have hbase : 1 ≤ (E + 1) ^ 2 := Nat.pow_pos (by omega)
  have hexp : (E + 1) ^ 2 + 1 ≤ C.Wd := by dsimp [E] at *; omega
  have hident : 2 * 2 ^ ((E + 1) ^ 2) = 2 ^ ((E + 1) ^ 2 + 1) := by rw [pow_succ]; omega
  exact (hp.trans_eq hident).le.trans (Nat.pow_le_pow_right (by decide) hexp)

end NearQuarticWires.StageLift
