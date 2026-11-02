import Proof.Quartic.StageRecovery.ModDispatch

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicGates.Close.Cells NearCubicGates.Close.Expand
open NearCubicGates.Close.Interfaces.Formats

/-- `lem:print`, paper/paper.tex: the local numerical
token envelope counts binary constant height and unary atom/exponent
work, without any unreduced formula-value height. -/
def tokenBound : Tok → ℕ
  | .const value => natBitLength value.natAbs + 1
  | .var atom => atom + 1
  | .pow exponent => exponent + 1
  | _ => 1

/-- `lem:print`, paper/paper.tex: the exact state
transition of one postfix payload preserves all non-input cursors and
the original formula metadata outside the named work variables. -/
def PayloadPost (a : DS VV MM) (q point : ℕ) (xs : List ℕ) (token : Tok)
    (b : DS VV MM) : Prop :=
  b.env stackVar = senc q ((modAlg q point).step xs token) ∧
  b.env modulusVar = q ∧ b.ip = a.ip + (payload token).length ∧
  (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) =
    (a.out, a.ram, a.rc, a.kin, a.kout, a.kc) ∧ Cst b ∧ Fr a b evalScratch

/-- `lem:print`, paper/paper.tex: every literal token
payload has an actual bounded binary-program implementation with the
exact general-modulus postfix semantics. -/
theorem modularPayload_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (q point : ℕ) (xs : List ℕ) (token : Tok) (rest : List Bool) (B : ℕ)
    (hq : 2 ≤ q) (haq : a.env modulusVar = q) (hap : a.env pointVar = point)
    (hstack : a.env stackVar = senc q xs) (hxs : ∀ x ∈ xs, x < q)
    (hdepth : q ^ (xs.length + 3) ≤ 2 ^ C.Wd)
    (hin : C.inp.drop a.ip = payload token ++ rest)
    (hB : tokenBound token ≤ B) (hwidth : B + 3 ≤ C.Wd) :
    Hs C (modularHandlers.get ⟨tagOf token, by
      simpa only [modularHandlers, List.length_cons, List.length_nil] using (tagOf_lt token)⟩)
      a (100 * B + 200)
      (PayloadPost a q point xs token) := by
  have hshort : q ^ (xs.length + 2) ≤ 2 ^ C.Wd :=
    (Nat.pow_le_pow_right (by omega) (by omega)).trans hdepth
  have hpow : C.Wd < 2 ^ C.Wd := Nat.lt_two_pow_self
  cases token with
  | const value =>
      refine (constantModHandler_spec C a hc q value xs rest hq haq hstack hxs hshort
        hin (by simp only [tokenBound] at hB; omega) (by omega)).mono ?_ ?_
      · simp only [tokenBound] at hB; omega
      · rintro b ⟨hbs, hbq, hbi, hbr, hbc, hbf⟩
        exact ⟨hbs, hbq, hbi, hbr, hbc, hbf⟩
  | var atom =>
      have hbits : natBitLength atom ≤ atom + 1 := nbl_le_self _
      have hbound : atom + 1 ≤ B := hB
      refine (variableModHandler_spec C a hc q point atom xs rest hq haq hap hstack hxs
        hshort hin (by omega) (by omega)).mono (by omega) ?_
      rintro b ⟨hbs, hbq, hbi, hbr, hbc, hbf⟩
      refine ⟨?_, hbq, hbi, hbr, hbc, hbf⟩
      simpa only [Alg.step, modAlg, pointBit, show 1 % q = 1 from Nat.mod_eq_of_lt (by omega)] using hbs
  | pow exponent =>
      have hbits : natBitLength exponent ≤ exponent + 1 := nbl_le_self _
      have hbound : exponent + 1 ≤ B := hB
      refine (powerPayloadHandler_spec C a hc q exponent xs rest hq haq hstack hxs
        hdepth hin (by omega) (by omega)).mono (by omega) ?_
      rintro b ⟨hbs, hbq, hbi, hbr, hbc, hbf⟩
      exact ⟨hbs, hbq, hbi, hbr, hbc, hbf⟩
  | add =>
      refine (binaryModHandler_spec C a hc false q xs hq hxs haq hstack hshort).mono (by omega) ?_
      rintro b ⟨hbs, hbq, hbsh, hbc, hbf⟩
      have hs := Same.of_sh hbsh
      exact ⟨hbs, hbq, by simpa [payload] using hs.ip,
        by simp only [hs.out, hs.ram, hs.rc, hs.kin, hs.kout, hs.kc], hbc, Fr.weaken hbf (by decide)⟩
  | mul =>
      refine (binaryModHandler_spec C a hc true q xs hq hxs haq hstack hshort).mono (by omega) ?_
      rintro b ⟨hbs, hbq, hbsh, hbc, hbf⟩
      have hs := Same.of_sh hbsh
      exact ⟨hbs, hbq, by simpa [payload] using hs.ip,
        by simp only [hs.out, hs.ram, hs.rc, hs.kin, hs.kout, hs.kc], hbc, Fr.weaken hbf (by decide)⟩
  | sub =>
      refine (subtractionModHandler_spec C a hc q xs hq hxs haq hstack hshort).mono (by omega) ?_
      rintro b ⟨hbs, hbq, hbsh, hbc, hbf⟩
      have hs := Same.of_sh hbsh
      exact ⟨hbs, hbq, by simpa [payload] using hs.ip,
        by simp only [hs.out, hs.ram, hs.rc, hs.kin, hs.kout, hs.kc], hbc, Fr.weaken hbf (by decide)⟩
  | neg =>
      refine (unaryModHandler_spec C a hc false q 0 xs hq hxs haq (by simp) (by simp)
        hstack hdepth).mono (by simp only [Bool.false_eq_true, if_false]; omega) ?_
      rintro b ⟨hbs, hbq, hbsh, hbc, hbf⟩
      have hs := Same.of_sh hbsh
      exact ⟨hbs, hbq, by simpa [payload] using hs.ip,
        by simp only [hs.out, hs.ram, hs.rc, hs.kin, hs.kout, hs.kc], hbc, Fr.weaken hbf (by decide)⟩

end NearQuarticWires.StageRecovery
