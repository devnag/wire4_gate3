import Proof.Quartic.StageMain.SampleDigits
import Proof.Quartic.StageGamma.FixedRead
import Proof.Wire_3_5.GFExists

/-!
# Reading the cached primitive polynomial

`imp:seed`, paper/paper.tex: the computed cache contains
exactly the low field-degree bits. The binary reader restores the monic
leading bit and preserves the seed and the certificate counters.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.SampleCells

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5
open NearCubicGates.Close.Cells

theorem modulus_low_add (p N : ℕ) (hp : GF.ModulusOk p N) :
    p % 2 ^ N + 2 ^ N = p := by
  have hbit : p / 2 ^ N % 2 = 1 := by
    have hh := hp.1
    rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff] at hh
    exact hh
  have hdiv : p / 2 ^ N < 2 := by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
    simpa [pow_succ, Nat.mul_comm] using hp.2
  have he : p / 2 ^ N = 1 := by
    rwa [Nat.mod_eq_of_lt hdiv] at hbit
  simpa [he] using Nat.mod_add_div p (2 ^ N)

def readFieldCache : St VV MM :=
  .seq (StageGamma.fixedRead ell modulus) (.op (.add modulus t1))

theorem readFieldCache_run (C : Ctx) (N p : ℕ) (hp : GF.ModulusOk p N)
    (rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hell : a.env ell = N) (hwidth : N + 2 ≤ C.Wd)
    (hin : C.inp.drop a.ip = binary N p ++ rest) :
    Hs C readFieldCache a (10 * N + 20) (fun b =>
      b.env modulus = p ∧ b.ip = a.ip + N ∧
      (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.out, a.ram, a.rc, a.kin, a.kout, a.kc) ∧ Cst b ∧
      Fr a b (StageGamma.fixedReadScratch modulus)) := by
  have hpfit : p < 2 ^ C.Wd :=
    hp.2.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  unfold readFieldCache
  refine Hs.seq (t1 := 10 * N + 18) (t2 := 1)
    (StageGamma.fixedRead_run C ell modulus (by decide) (by decide)
      a hc N p rest hell (by omega) hin) ?_
  rintro b ⟨hb, ht1, hbi, hrest, hbc, hfr⟩
  refine (hs_add C modulus t1 b (by decide)
    (by rw [hb, ht1, modulus_low_add p N hp]; exact hpfit)).mono le_rfl ?_
  rintro d rfl
  exact ⟨by rw [DS.set_env_self, hb, ht1, modulus_low_add p N hp], hbi, hrest,
    Cst.of_fr (T := StageGamma.fixedReadScratch modulus) hbc
      (Fr.set b _ (by simp [StageGamma.fixedReadScratch])) (by decide),
    hfr.trans (Fr.set b _ (by simp [StageGamma.fixedReadScratch]))⟩

theorem readFirstPrimitive_run (C : Ctx) (N : ℕ) (hN : 1 ≤ N)
    (rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hell : a.env ell = N) (hwidth : N + 2 ≤ C.Wd)
    (hin : C.inp.drop a.ip = binary N (GF.firstPrimitive N) ++ rest) :
    Hs C readFieldCache a (10 * N + 20) (fun b =>
      b.env modulus = GF.firstPrimitive N ∧ b.ip = a.ip + N ∧
      (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.out, a.ram, a.rc, a.kin, a.kout, a.kc) ∧ Cst b ∧
      Fr a b (StageGamma.fixedReadScratch modulus)) :=
  readFieldCache_run C N (GF.firstPrimitive N) (GF.firstPrimitive_cert N hN).2.1
    rest a hc hell hwidth hin

end NearQuarticWires.StageMain.SampleCells
