import Proof.Quartic.StageGamma.DigitRegisters
import Proof.Quartic.StageGamma.LabelPrepare

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageGamma

open NearCubicGates.Close.Cells

/-- `cor:conditional`, paper/paper.tex: the eight
real sample-label decrements are a fixed finite control sequence. -/
def prepareLabelsList : List (Fin 8) → St VV MM
  | [] => skipS
  | slot :: slots => .seq (prepareLabel slot) (prepareLabelsList slots)

/-- `cor:conditional`, paper/paper.tex: distinct
choice slots occupy distinct physical sample-label variables. -/
theorem gammaLabel_injective : Function.Injective gammaLabel := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  dsimp [gammaLabel] at this
  omega

/-- `cor:conditional`, paper/paper.tex: the actual
label destination set does not overwrite any true radix digit. -/
theorem gammaDigit_not_labels (slot : Fin 8) (slots : List (Fin 8)) :
    gammaDigit slot ∉ slots.map gammaLabel ++ [vJ] := by
  simp only [List.mem_append, List.mem_map, List.mem_singleton, not_or, not_exists]
  constructor
  · intro i ⟨_, h⟩
    have := congrArg Fin.val h
    dsimp [gammaLabel, gammaDigit] at this
    have hi := i.isLt
    have hs := slot.isLt
    omega
  · fin_cases slot <;> decide

/-- `cor:conditional` and `prop:time`, paper/paper.tex: actual finite label preparation computes every selected
original sample index and preserves all source fields and cached data. -/
theorem prepareLabelsList_run (C : Ctx) (slots : List (Fin 8)) (hn : slots.Nodup)
    (Q : ℕ) (choice : Cycle.GammaChoice Q) (a : DS VV MM) (hc : Cst a)
    (hdigits : ∀ slot, a.env (gammaDigit slot) = (choice slot).val) :
    Hs C (prepareLabelsList slots) a (5 * slots.length + 1) (fun b =>
      (∀ slot ∈ slots, b.env (gammaLabel slot) = (choice slot).val - 1) ∧
      Same a b ∧ Cst b ∧ Fr a b (slots.map gammaLabel ++ [vJ])) := by
  induction slots generalizing a with
  | nil =>
    refine Hs.mono (skip_spec a) le_rfl ?_
    rintro b rfl
    exact ⟨by simp, Same.set _ _ _,
      Cst.of_fr (T := [vJ]) hc (Fr.set a 0 (by simp)) (by decide),
      Fr.set a _ (by simp)⟩
  | cons slot slots ih =>
    have hnd : slot ∉ slots ∧ slots.Nodup := by simpa using hn
    refine Hs.mono (Hs.seq (t1 := 4) (t2 := 5 * slots.length + 1)
      (prepareLabel_run C slot a hc) ?_) (by simp; omega) (fun _ h => h)
    intro b ⟨hb, hs, hbc, hfr⟩
    have hbd : ∀ i, b.env (gammaDigit i) = (choice i).val := by
      intro i
      rw [hfr (gammaDigit i) (by
        simpa only [List.map_singleton, List.singleton_append] using gammaDigit_not_labels i [slot])]
      exact hdigits i
    refine Hs.mono (ih hnd.2 b hbc hbd) le_rfl ?_
    intro e ⟨he, hes, hec, hef⟩
    refine ⟨?_, hs.trans hes, hec,
      (hfr.weaken (by
        intro y hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with h | h
        · simp [h]
        · simp [h])).trans (hef.weaken (by
          intro y hy
          change y ∈ gammaLabel slot :: (slots.map gammaLabel ++ [vJ])
          exact List.mem_cons_of_mem _ hy))⟩
    intro i hi
    rcases List.mem_cons.mp hi with hhead | hi
    · subst i
      rw [hef (gammaLabel slot) (by
        simp only [List.mem_append, List.mem_map, List.mem_singleton, not_or, not_exists]
        constructor
        · intro j ⟨hj, heq⟩
          exact hnd.1 ((gammaLabel_injective heq) ▸ hj)
        · fin_cases slot <;> decide), hb, hdigits]
    · exact he i hi

/-- `cor:conditional`, paper/paper.tex: all eight
sample-label decrements are emitted by one finite physical program. -/
def prepareLabels : St VV MM := prepareLabelsList (List.finRange 8)

/-- `cor:conditional` and `prop:time`, paper/paper.tex: all eight actual sample labels are available after exactly
bounded ordinary source-language work, including Q=0. -/
theorem prepareLabels_run (C : Ctx) (Q : ℕ) (choice : Cycle.GammaChoice Q)
    (a : DS VV MM) (hc : Cst a)
    (hdigits : ∀ slot, a.env (gammaDigit slot) = (choice slot).val) :
    Hs C prepareLabels a 41 (fun b =>
      (∀ slot, b.env (gammaLabel slot) = (choice slot).val - 1) ∧
      Same a b ∧ Cst b ∧ Fr a b ((List.finRange 8).map gammaLabel ++ [vJ])) := by
  refine Hs.mono (prepareLabelsList_run C (List.finRange 8) (List.nodup_finRange _) Q choice
    a hc hdigits) (by simp) ?_
  intro b ⟨hb, hs, hbc, hf⟩
  exact ⟨fun slot => hb slot (List.mem_finRange _), hs, hbc, hf⟩

end NearQuarticWires.StageGamma
