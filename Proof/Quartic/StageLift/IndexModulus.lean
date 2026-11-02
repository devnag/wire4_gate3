import Proof.Quartic.StageCertTests.ParameterSelect
import Proof.Quartic.StageLift.StoreFrame
import Proof.Gates.Cells.Arith

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicGates.Close.Cells
open NearQuarticWires.StageRecovery

/-- `lem:residue` and `sec:params`, paper/paper.tex: the actual print-index prime occupies a source register
before the index bank is normalized or the Formula source is generated. -/
def indexPrimeVar : Fin VV := 126

/-- `lem:residue` and `sec:params`, paper/paper.tex: the lift exponent is read from its actual scalar record. -/
def indexExponentVar : Fin VV := 125

/-- `lem:residue`, paper/paper.tex: fetch the
retained exponent at its public scalar position and compute p^e by
the existing physical binary-arithmetic power program. -/
def computeIndexModulus : St VV MM :=
  .seq (StageCertTests.selectParameter 26 indexExponentVar)
    (powP indexPrimeVar indexExponentVar StageRecovery.modulusVar)

/-- `lem:residue`, paper/paper.tex: the modulus
calculation accesses only the actual retained parameter store. In
particular it preserves the cursor of the normalized index bank. -/
theorem computeIndexModulus_avoids (store : Fin MM) (hne : store ≠ parameterStore) :
    avoidsStore store computeIndexModulus := by
  have hskip : ∀ n, avoidsStore store (StageCertTests.skipParameterRecords n) := by
    intro n
    induction n with
    | zero => trivial
    | succ n ih => exact ⟨hne, ih⟩
  exact ⟨⟨hne, hskip 26, hne⟩, by trivial⟩

/-- `lem:residue`, paper/paper.tex: the recovery
modulus is physically computed from the original index prime and
decoded parameter store, rather than supplied as a computed field. -/
theorem computeIndexModulus_spec (C : Ctx) (p : Cells.Parameters) (prime : ℕ)
    (a : DS VV MM) (hc : Cst a)
    (hparams : a.ram parameterStore = parameterScalars p)
    (hprime : a.env indexPrimeVar = prime) (hp : 2 ≤ prime)
    (hfit : 2 * prime ^ p.e ≤ 2 ^ C.Wd) :
    Hs C computeIndexModulus a (a.rc parameterStore + 7 * p.e + 66) (fun b =>
      b.env StageRecovery.modulusVar = prime ^ p.e ∧ b.env indexExponentVar = p.e ∧
      b.env indexPrimeVar = prime ∧ b.rc parameterStore = 27 ∧ b.ram = a.ram ∧
      (b.ip, b.out, b.kin, b.kout, b.kc) = (a.ip, a.out, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b [indexExponentVar, StageRecovery.modulusVar, vJ, a1, c4]) := by
  have hqpos : 0 < prime ^ p.e := pow_pos (by omega : 0 < prime) _
  have hqfit : prime ^ p.e < 2 ^ C.Wd := by omega
  have hefit : p.e < 2 ^ C.Wd :=
    lt_of_lt_of_le (Nat.lt_two_pow_self (n := p.e))
      ((Nat.pow_le_pow_left hp p.e).trans hqfit.le)
  unfold computeIndexModulus
  have hs := StageCertTests.selectParameter_spec C a (parameterScalars p) 26
    (by rw [parameterScalars_length]; decide) indexExponentVar hparams
  refine (Hs.seq (t1 := a.rc parameterStore + 57) (t2 := 7 * p.e + 8) hs
    fun b ⟨hbe, hbcursor, hbram, hbsh, hbf⟩ => ?_).mono (by omega) (fun _ h => h)
  have he : b.env indexExponentVar = p.e := by simpa [parameterScalars,
    parameterHeadScalars, parameterTailScalars, rationalFields, integerFields] using hbe
  have hbprime : b.env indexPrimeVar = prime := by rw [hbf _ (by decide)]; exact hprime
  have hbc : Cst b := Cst.of_fr hc hbf (by decide)
  have hpw := powP_spec (C := C) indexPrimeVar indexExponentVar StageRecovery.modulusVar
    (by decide) b (by
      intro k hk
      rw [he] at hk
      rw [hbprime]
      exact lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) hk) hqfit)
    (by rw [he]; exact hefit) (by omega)
  rw [he] at hpw
  refine hpw.mono (by omega) ?_
  rintro d ⟨hdq, hdsh, hdf⟩
  have hsame := Same.of_sh hdsh
  have hf : Fr a d [indexExponentVar, StageRecovery.modulusVar, vJ, a1, c4] :=
    (hbf.weaken (by simp)).trans (hdf.weaken (by simp))
  refine ⟨?_, ?_, ?_, ?_, hsame.ram.trans hbram, ?_, Cst.of_fr hbc hdf (by decide), hf⟩
  · simpa only [hbprime, he] using hdq
  · rw [hdf indexExponentVar (by decide), he]
  · rw [hdf indexPrimeVar (by decide), hbprime]
  · rw [hsame.rc, hbcursor]
  · rw [hsame.ip, hsame.out, hsame.kin, hsame.kout, hsame.kc]
    exact hbsh

/-- `lem:residue`, paper/paper.tex: the physical
prime-power computation also exposes its complete memory-cursor frame,
so index, witness, Gamma and finite-call sources stay at their real positions. -/
theorem computeIndexModulus_framed_spec (C : Ctx) (p : Cells.Parameters) (prime : ℕ)
    (a : DS VV MM) (hc : Cst a)
    (hparams : a.ram parameterStore = parameterScalars p)
    (hprime : a.env indexPrimeVar = prime) (hp : 2 ≤ prime)
    (hfit : 2 * prime ^ p.e ≤ 2 ^ C.Wd) :
    Hs C computeIndexModulus a (a.rc parameterStore + 7 * p.e + 66) (fun b =>
      (b.env StageRecovery.modulusVar = prime ^ p.e ∧ b.env indexExponentVar = p.e ∧
      b.env indexPrimeVar = prime ∧ b.rc parameterStore = 27 ∧ b.ram = a.ram ∧
      (b.ip, b.out, b.kin, b.kout, b.kc) = (a.ip, a.out, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b [indexExponentVar, StageRecovery.modulusVar, vJ, a1, c4]) ∧ b.rc = Function.update a.rc parameterStore 27) := by
  obtain ⟨b, n, he, hn, hb⟩ := computeIndexModulus_spec C p prime a hc hparams hprime hp hfit
  refine ⟨b, n, he, hn, hb, ?_⟩
  have hcur : b.rc parameterStore = 27 := hb.2.2.2.1
  funext store
  by_cases hs : store = parameterStore
  · subst store
    simp [hcur]
  · rw [Function.update_of_ne hs]
    exact (avoidsStore_spec he (computeIndexModulus_avoids store hs)).2

end NearQuarticWires.StageLift
