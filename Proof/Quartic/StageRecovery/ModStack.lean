import Proof.Quartic.StageRecovery.ModArithmetic
import Proof.Gates.Expand.PassDW

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicGates.Close.Cells NearCubicGates.Close.Expand

/-- `lem:print`, paper/paper.tex: the postfix stack is
encoded in the recovery-modulus radix on an actual binary variable. -/
def stackVar : Fin VV := ⟨70, by decide⟩

/-- `lem:print`, paper/paper.tex: one stack pop is
literal binary division, preserving the modulus and the other operand. -/
def popModStack (target : Fin VV) : St VV MM :=
  .seq (.op (.dm stackVar modulusVar quotientVar target))
    (.op (.copy stackVar quotientVar))

/-- `lem:print`, paper/paper.tex: the actual pop returns
the top reduced residue and retains the complete remaining stack. -/
theorem popModStack_spec (C : Ctx) (a : DS VV MM) (target : Fin VV)
    (htarget : target ≠ stackVar ∧ target ≠ modulusVar ∧ target ≠ quotientVar)
    (q : ℕ) (xs : List ℕ) (hq : 0 < q) (hxs : ∀ x ∈ xs, x < q)
    (haq : a.env modulusVar = q) (hstack : a.env stackVar = senc q xs)
    (hfit : 2 * q ≤ 2 ^ C.Wd) :
    Hs C (popModStack target) a 3 (fun b =>
      b.env target = xs.headD 0 ∧ b.env stackVar = senc q xs.tail ∧
      b.sh = a.sh ∧ Fr a b [target, stackVar, quotientVar]) := by
  unfold popModStack
  refine Hs.seq (t2 := 1) (hs_dm C stackVar modulusVar quotientVar target a
    (by decide) (by decide) (Ne.symm htarget.1) (by decide)
    (Ne.symm htarget.2.1) (Ne.symm htarget.2.2)
    (by rw [haq]; exact hq) (by rw [haq]; exact hfit)) fun b hb => ?_
  subst b
  refine (hs_copy C stackVar quotientVar _ (by decide)).mono le_rfl ?_
  rintro b rfl
  have hx : xs.headD 0 < q := Alg.headD_lt hq xs hxs
  have hdiv : senc q xs / q = senc q xs.tail := by
    rw [senc_headD q xs, senc_div q _ _ hx]
  have hmod : senc q xs % q = xs.headD 0 := by
    rw [senc_headD q xs, senc_mod q _ _ hx]
  refine ⟨?_, ?_, rfl, ?_⟩
  · simp only [DS.set_env_ne _ _ htarget.1, DS.set_env_self, hstack, haq, hmod]
  · simp only [DS.set_env_self, DS.set_env_ne _ _ (Ne.symm htarget.2.2),
      hstack, haq, hdiv]
  · exact Fr.trans (Fr.set _ _ (by simp))
      (Fr.trans (Fr.set _ _ (by simp)) (Fr.set _ _ (by simp)))

/-- `lem:print`, paper/paper.tex: a reduced result is
pushed by one radix multiplication and addition. -/
def pushModStack : St VV MM :=
  .seq (.op (.mul stackVar modulusVar productVar))
    (.seq (.op (.add productVar leftVar)) (.op (.copy stackVar productVar)))

/-- `lem:print`, paper/paper.tex: the actual push retains
every reduced residue already stored in the postfix stack. -/
theorem pushModStack_spec (C : Ctx) (a : DS VV MM) (q value : ℕ) (xs : List ℕ)
    (haq : a.env modulusVar = q) (hav : a.env leftVar = value)
    (hstack : a.env stackVar = senc q xs)
    (hfit : senc q (value :: xs) < 2 ^ C.Wd) :
    Hs C pushModStack a 5 (fun b =>
      b.env stackVar = senc q (value :: xs) ∧ b.sh = a.sh ∧
      Fr a b [stackVar, productVar]) := by
  have hmul : a.env stackVar * a.env modulusVar < 2 ^ C.Wd := by
    rw [hstack, haq]
    simp only [senc] at hfit
    nlinarith
  unfold pushModStack
  refine Hs.seq (t2 := 3) (hs_mul C stackVar modulusVar productVar a
    (by decide) (by decide) (by decide) hmul) fun b hb => ?_
  subst b
  refine Hs.seq (t2 := 1) (hs_add C productVar leftVar _ (by decide) (by
    simp (config := {decide := true}) only [DS.set, Function.update_self,
      Function.update_of_ne (show leftVar ≠ productVar by decide), hstack, haq, hav]
    simp only [senc] at hfit
    nlinarith)) fun b hb => ?_
  subst b
  refine (hs_copy C stackVar productVar _ (by decide)).mono le_rfl ?_
  rintro b rfl
  refine ⟨?_, rfl, ?_⟩
  · simp (config := {decide := true}) only [DS.set, Function.update_self,
      Function.update_of_ne (show leftVar ≠ productVar by decide), hstack, haq, hav, senc]
    ring
  · exact Fr.trans (Fr.set _ _ (by decide))
      (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide)))

end NearQuarticWires.StageRecovery
