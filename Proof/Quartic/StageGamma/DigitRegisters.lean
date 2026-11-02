import Proof.Quartic.StageGamma.CachedBudget
import Proof.Quartic.StageGamma.Radix

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageGamma

open NearCubicWires
open NearCubicGates.Close.Cells

/-- `cor:conditional`, paper/paper.tex: the true
radix base is Q+1, including base one when Q=0. -/
def gammaBase : Fin VV := ⟨96, by decide⟩

/-- `cor:conditional`, paper/paper.tex: the exact
coefficient address is divided eight times without a field-label loop. -/
def gammaWork : Fin VV := ⟨97, by decide⟩

/-- `cor:conditional`, paper/paper.tex: fixed
quotient scratch for one exact base-Q+1 coordinate. -/
def gammaQuotient : Fin VV := ⟨98, by decide⟩

/-- `cor:conditional`, paper/paper.tex: one real
division computes a digit and advances the remaining address. -/
def readChoiceDigit (destination : Fin VV) : St VV MM :=
  .seq (.op (.dm gammaWork gammaBase gammaQuotient destination))
    (.op (.copy gammaWork gammaQuotient))

/-- `cor:conditional`, paper/paper.tex: the fixed
finite coordinate list determines the whole physical radix decoder. -/
def readChoiceDigits : List (Fin VV) → St VV MM
  | [] => skipS
  | x :: xs => .seq (readChoiceDigit x) (readChoiceDigits xs)

/-- `cor:conditional`, paper/paper.tex: only the
actual target digits and two arithmetic scratch variables may change. -/
def choiceDigitScratch (xs : List (Fin VV)) : List (Fin VV) :=
  gammaWork :: gammaQuotient :: vJ :: xs

/-- `cor:conditional` and `prop:time`, paper/paper.tex: repeated actual divisions write the exact unpadded radix
digits, with a constant charge per coordinate and base one fully included. -/
theorem readChoiceDigits_run (C : Ctx) (xs : List (Fin VV)) (hn : xs.Nodup)
    (hsafe : ∀ x ∈ xs, x ∉ [gammaWork, gammaBase, gammaQuotient, vJ, vZ, v1, v2])
    (a : DS VV MM) (hc : Cst a) (base value : ℕ) (hbase : 1 ≤ base)
    (hb : a.env gammaBase = base) (hv : a.env gammaWork = value)
    (hwidth : 2 * base ≤ 2 ^ C.Wd) :
    Hs C (readChoiceDigits xs) a (4 * xs.length + 1) (fun b =>
      (∀ i : Fin xs.length, b.env xs[i] = value / base ^ i.val % base) ∧
      b.env gammaWork = value / base ^ xs.length ∧ Same a b ∧ Cst b ∧
      Fr a b (choiceDigitScratch xs)) := by
  induction xs generalizing a value with
  | nil =>
    refine Hs.mono (skip_spec a) le_rfl ?_
    rintro b rfl
    exact ⟨fun i => i.elim0, by rw [DS.set_env_ne _ _ (by decide), hv]; simp,
      Same.set _ _ _, Cst.of_fr (T := [vJ]) hc (Fr.set a 0 (by simp)) (by decide),
      Fr.set a _ (by simp [choiceDigitScratch])⟩
  | cons x xs ih =>
    have hx := hsafe x (by simp)
    have hxw : x ≠ gammaWork := by intro h; exact hx (by simp [h])
    have hxb : x ≠ gammaBase := by intro h; exact hx (by simp [h])
    have hxq : x ≠ gammaQuotient := by intro h; exact hx (by simp [h])
    have hnd : x ∉ xs ∧ xs.Nodup := by simpa using hn
    have hconst : vZ ∉ choiceDigitScratch (x :: xs) ∧
        v1 ∉ choiceDigitScratch (x :: xs) ∧ v2 ∉ choiceDigitScratch (x :: xs) := by
      have hh : ∀ z ∈ [vZ, v1, v2], z ∉ x :: xs := by
        intro z hz hmem
        have hnz := hsafe z hmem
        exact hnz (by simp only [List.mem_cons, List.not_mem_nil, or_false] at *; tauto)
      simpa only [choiceDigitScratch, List.mem_cons, List.not_mem_nil, or_false, not_or] using
        (show (vZ ≠ gammaWork ∧ vZ ≠ gammaQuotient ∧ vZ ≠ vJ ∧ vZ ∉ x :: xs) ∧
          (v1 ≠ gammaWork ∧ v1 ≠ gammaQuotient ∧ v1 ≠ vJ ∧ v1 ∉ x :: xs) ∧
          (v2 ≠ gammaWork ∧ v2 ≠ gammaQuotient ∧ v2 ≠ vJ ∧ v2 ∉ x :: xs) from
          ⟨⟨by decide, by decide, by decide, hh vZ (by simp)⟩,
            ⟨by decide, by decide, by decide, hh v1 (by simp)⟩,
            ⟨by decide, by decide, by decide, hh v2 (by simp)⟩⟩)
    unfold readChoiceDigits readChoiceDigit
    refine Hs.mono (Hs.seq (t1 := 3) (t2 := 4 * xs.length + 1)
      (Hs.seq (t1 := 1) (t2 := 1)
        (R2 := fun d => d =
          ((a.set gammaQuotient (a.env gammaWork / a.env gammaBase)).set x
            (a.env gammaWork % a.env gammaBase)).set gammaWork
              (((a.set gammaQuotient (a.env gammaWork / a.env gammaBase)).set x
                (a.env gammaWork % a.env gammaBase)).env gammaQuotient))
        (hs_dm C gammaWork gammaBase gammaQuotient x a
          (by decide) (by decide) hxw.symm (by decide) hxb.symm hxq.symm
          (by rw [hb]; omega) (by rw [hb]; exact hwidth))
        (fun b hbe => ?_)) ?_) (by simp; omega) (fun _ h => h)
    · subst hbe
      exact hs_copy C gammaWork gammaQuotient _ (by decide)
    · intro b hbstate
      subst hbstate
      let b := ((a.set gammaQuotient (a.env gammaWork / a.env gammaBase)).set x
        (a.env gammaWork % a.env gammaBase)).set gammaWork
          (((a.set gammaQuotient (a.env gammaWork / a.env gammaBase)).set x
            (a.env gammaWork % a.env gammaBase)).env gammaQuotient)
      have hf : Fr a b (choiceDigitScratch (x :: xs)) :=
        (Fr.set a _ (by simp [choiceDigitScratch])).trans
          ((Fr.set _ _ (by simp [choiceDigitScratch])).trans
            (Fr.set _ _ (by simp [choiceDigitScratch])))
      have hbc : Cst b := Cst.of_fr hc hf hconst
      have hbb : b.env gammaBase = base := by
        rw [hf gammaBase (by
          have hh : gammaBase ∉ x :: xs := by
            intro hh
            exact (hsafe gammaBase hh) (by simp)
          change gammaBase ∉ gammaWork :: gammaQuotient :: vJ :: x :: xs
          intro hm
          rcases List.mem_cons.mp hm with heq | hm
          · exact (by decide : gammaBase ≠ gammaWork) heq
          rcases List.mem_cons.mp hm with heq | hm
          · exact (by decide : gammaBase ≠ gammaQuotient) heq
          rcases List.mem_cons.mp hm with heq | hm
          · exact (by decide : gammaBase ≠ vJ) heq
          exact hh hm)]
        exact hb
      have hbw : b.env gammaWork = value / base := by
        simp [b, hxq.symm, hv, hb]
      have hbx : b.env x = value % base := by
        simp [b, hxw, hv, hb]
      refine Hs.mono (ih hnd.2 (fun y hy => hsafe y (by simp [hy])) b hbc
        (value / base) hbb hbw) le_rfl ?_
      intro e ⟨he, hew, hes, hec, hef⟩
      refine ⟨?_, ?_, (Same.set a _ _).trans ((Same.set _ _ _).trans
        ((Same.set _ _ _).trans hes)), hec,
        hf.trans (hef.weaken (by
          intro y hy
          simp only [choiceDigitScratch, List.mem_cons] at hy ⊢
          rcases hy with h | h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr (Or.inr h)))))⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · change e.env x = value / base ^ 0 % base
          rw [hef x (by
            have hxj : x ≠ vJ := by intro h; exact hx (by simp [h])
            simp [choiceDigitScratch, hxw, hxq, hxj, hnd.1]), hbx]
          simp
        · simpa [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm] using he j
      · rw [hew, Nat.div_div_eq_div_mul, List.length_cons, pow_succ, Nat.mul_comm base]

/-- `cor:conditional`, paper/paper.tex: the low-first
coordinate convention is an exact equivalence on the true `(Q+1)^8` space. -/
def littleChoiceEquiv (Q : ℕ) : Fin ((Q + 1) ^ 8) ≃ Cycle.GammaChoice Q :=
  finFunctionFinEquiv.symm

/-- `cor:conditional`, paper/paper.tex: each actual
division destination is the corresponding true sample-choice digit. -/
theorem littleChoice_digit (Q : ℕ) (address : Fin ((Q + 1) ^ 8)) (slot : Fin 8) :
    (littleChoiceEquiv Q address slot).val = address.val / (Q + 1) ^ slot.val % (Q + 1) := by
  rfl

end NearQuarticWires.StageGamma
