import Proof.Quartic.StageMain.EntryRequest
import Proof.Wire_3_5.SeedFixSampObjective

/-!
# Numeric row and column of the sampled field value

`imp:seed`, paper/paper.tex, and Step 4 of
`sec:algorithm`: the low half of the projected field
bits is the column and the next half is the row. Higher field bits are
discarded by the projection. These identities include the one-element
side and require no bound on the original natural number.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.EntryCoordinates

open NearCubicWires.WireExponent3_5
open Sampler

theorem ofVec_testBits (n v : ℕ) :
    ofVec (fun i : Fin n => GF.bitF (v.testBit i)) = v % 2 ^ n := by
  apply freeVec_injOn _ _ (ofVec_lt _) (Nat.mod_lt _ (Nat.two_pow_pos _))
  rw [freeVec_ofVec]
  funext i
  simp only [freeVec, Nat.testBit_mod_two_pow, decide_eq_true i.isLt, Bool.true_and]

theorem cellEquiv_value (P : SeedParams) (v : ℕ) :
    SeedFix.cellNumC (P.cellEquiv (fun b => GF.bitF (v.testBit b))) = v % (P.N * P.N) := by
  rw [SeedFix.cellNumC_eq P, cellNum, Equiv.symm_apply_apply, ofVec_testBits]
  rw [two_mul, pow_add]

theorem cellEquiv_fst_value (P : SeedParams) (v : ℕ) :
    (P.cellEquiv (fun b => GF.bitF (v.testBit b))).1.val = (v / P.N) % P.N := by
  have h := congrArg (fun z => z / P.N) (cellEquiv_value P v)
  rw [SeedFix.cellNumC, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt (P.cellEquiv (fun b => GF.bitF (v.testBit b))).2.isLt,
    Nat.zero_add, Nat.mod_mul_right_div_self] at h
  exact h

theorem cellEquiv_snd_value (P : SeedParams) (v : ℕ) :
    (P.cellEquiv (fun b => GF.bitF (v.testBit b))).2.val = v % P.N := by
  have h := congrArg (fun z => z % P.N) (cellEquiv_value P v)
  rw [SeedFix.cellNumC, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (P.cellEquiv (fun b => GF.bitF (v.testBit b))).2.isLt,
    Nat.mod_mul_right_mod] at h
  exact h

theorem entry_side {B1 B2 : ℕ} (r : EntryRequest B1 B2) :
    (entryCall r).seed.N = r.selected.1.N := by
  change 2 ^ (r.selected.1.k / 2) = r.selected.1.N
  exact (Cells.prepare_spec _ r.selected.1 r.selected.2).N_eq.symm

theorem entryPosition_fst_value {B1 B2 : ℕ} (r : EntryRequest B1 B2) :
    (entryPosition r).1.val = (r.fieldValue.val / r.selected.1.N) % r.selected.1.N := by
  have h := cellEquiv_fst_value (entryCall r).seed r.fieldValue.val
  exact h.trans (congrArg (fun N => r.fieldValue.val / N % N) (entry_side r))

theorem entryPosition_snd_value {B1 B2 : ℕ} (r : EntryRequest B1 B2) :
    (entryPosition r).2.val = r.fieldValue.val % r.selected.1.N := by
  have h := cellEquiv_snd_value (entryCall r).seed r.fieldValue.val
  exact h.trans (congrArg (fun N => r.fieldValue.val % N) (entry_side r))

end NearQuarticWires.StageMain.EntryCoordinates
