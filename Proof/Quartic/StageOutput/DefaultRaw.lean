import Proof.Quartic.StageOutput.Default
import Proof.Quartic.StageOutput.Framing
import Proof.Quartic.Program.Pipe

/-!
# Copying an encoded output after its branch tag

Paper: `sec:params`, paper/paper.tex, and
`prop:time`. The ordinary machine consumes the tagged scalar
word directly. It writes the two rational numbers in their original exact
encoding, after a paid conversion to the arithmetic input format.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageOutput

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces

def defaultBudget (L : ℕ) : ℕ :=
  1600 * (L + 1) + 4 * budgetOf VV 4 L (100 * (L + 1)) + 12

/-- The six-word copier with its exact raw input and output. -/
noncomputable def defaultRaw :
    WordFunction {xs : List ℕ // xs.length = 6}
      (fun xs => false :: xs.1.flatMap natWord) (fun xs => xs.1.flatMap natWord)
      (fun xs => defaultBudget (false :: xs.1.flatMap natWord).length) := by
  let f : WordFunction {xs : List ℕ // xs.length = 6}
      (fun xs => false :: xs.1.flatMap natWord)
      (fun xs => frame (frame (false :: xs.1.flatMap natWord) ++ frame []))
      (fun xs => 400 * ((false :: xs.1.flatMap natWord).length + 1)) :=
    ⟨arithmeticFraming.program, fun xs => arithmeticFraming.realizes (false :: xs.1.flatMap natWord)⟩
  have h := Program.WordFunction.pipe f defaultCodec
  convert h using 1
  funext xs
  simp [defaultBudget]
  ring

/-- The six integer fields of a pair of reduced rationals. -/
def rationalDigits (q : ℚ × ℚ) : List ℕ :=
  [if q.1.num < 0 then 1 else 0, q.1.num.natAbs, q.1.den,
   if q.2.num < 0 then 1 else 0, q.2.num.natAbs, q.2.den]

theorem rationalDigits_length (q : ℚ × ℚ) : (rationalDigits q).length = 6 := rfl

theorem rationalDigits_word (q : ℚ × ℚ) : (rationalDigits q).flatMap natWord = outputWord q := by
  simp [rationalDigits, outputWord, ratWord, NearCubicGates.Close.Interfaces.intWord,
    List.append_assoc]

/-- Direct physical copying of an encoded rational pair after the false tag. -/
noncomputable def defaultPair :
    WordFunction (ℚ × ℚ) (fun q => false :: outputWord q) outputWord
      (fun q => defaultBudget (outputWord q).length.succ) where
  program := defaultRaw.program
  realizes q := by
    have h := defaultRaw.realizes ⟨rationalDigits q, rationalDigits_length q⟩
    simpa only [rationalDigits_word, List.length_cons] using h

theorem defaultBudget_polynomial (L : ℕ) :
    defaultBudget L ≤ 100000000000 * (L + 1) ^ 9 := by
  have hL : 1 ≤ L + 1 := by omega
  have h4 : (L + 1) ^ 4 ≤ (L + 1) ^ 9 := Nat.pow_le_pow_right hL (by omega)
  have h1 : L + 1 ≤ (L + 1) ^ 9 := by
    simpa using Nat.pow_le_pow_right (n := L + 1) hL (by omega : 1 ≤ 9)
  have hX : L + 5 ≤ 5 * (L + 1) := by omega
  have hsetup : setupCost VV 4 L ≤ 32250000 * (L + 1) ^ 4 := by
    unfold setupCost VV
    have h := Nat.pow_le_pow_left hX 4
    rw [mul_pow] at h
    norm_num at h ⊢
    nlinarith
  have hWd : wdOf 4 L + 1 ≤ 626 * (L + 1) ^ 4 := by
    have h := Nat.pow_le_pow_left (show L + 4 ≤ 5 * (L + 1) by omega) 4
    rw [mul_pow] at h
    have hpos : 1 ≤ (L + 1) ^ 4 := one_le_pow₀ hL
    unfold wdOf
    norm_num at h
    omega
  have hKC : KC (wdOf 4 L) ≤ 195938000 * (L + 1) ^ 8 := by
    have h := Nat.pow_le_pow_left hWd 2
    unfold KC
    calc 500 * (wdOf 4 L + 1) ^ 2 ≤ 500 * (626 * (L + 1) ^ 4) ^ 2 :=
        Nat.mul_le_mul_left _ h
      _ = 195938000 * (L + 1) ^ 8 := by ring
  have hprod : 100 * (L + 1) * KC (wdOf 4 L) ≤ 19593800000 * (L + 1) ^ 9 := by
    calc 100 * (L + 1) * KC (wdOf 4 L) ≤
        100 * (L + 1) * (195938000 * (L + 1) ^ 8) := Nat.mul_le_mul_left _ hKC
      _ = 19593800000 * (L + 1) ^ 9 := by ring
  unfold defaultBudget budgetOf
  nlinarith

end NearQuarticWires.StageOutput
