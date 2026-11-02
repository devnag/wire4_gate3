import Proof.Quartic.StageRecovery.InputReturn

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: a first pass reaches
the appended native family by reading each original Formula bit once. -/
def inputForwardProgram : St VV MM :=
  forS inputReturnIndex tokenLengthVar (.op (.rdI vJ))

/-- `lem:print`, paper/paper.tex: the literal forward
pass pays one real input operation per original token byte, retaining
all stores and outputs before the native family packet is parsed. -/
theorem inputForwardProgram_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (bits suffix : List Bool) (hlen : a.env tokenLengthVar = bits.length)
    (hin : C.inp.drop a.ip = bits ++ suffix) (hfit : bits.length < 2 ^ C.Wd) :
    Hs C inputForwardProgram a (5 * bits.length + 4) (fun b =>
      b.ip = a.ip + bits.length ∧ inputRest b = inputRest a ∧
      Cst b ∧ Fr a b [inputReturnIndex, vJ]) := by
  let I : ℕ → DS VV MM → Prop := fun k b =>
    b.ip = a.ip + k ∧ inputRest b = inputRest a ∧ Cst b ∧ Fr a b [inputReturnIndex, vJ]
  unfold inputForwardProgram
  refine (forS_spec' (C := C) inputReturnIndex tokenLengthVar (by decide) (.op (.rdI vJ))
    a bits.length hfit I 1 ?_ ⟨by simp, rfl, hc, Fr.refl _ _⟩ hlen ?_).mono (by omega) ?_
  · intro k b value ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, Cst.of_fr (T := [inputReturnIndex]) h3 (Fr.set _ _ (by decide)) (by decide),
      Fr.trans h4 (Fr.set _ _ (by simp))⟩
  · intro k hk b ⟨h1, h2, h3, h4⟩ hbi hbl
    refine (hs_rdI C vJ b (by rw [h1]; exact lt_of_drop hin k hk)).mono le_rfl ?_
    rintro d rfl
    have hf : Fr b ({ b.set vJ (bitOf C.inp b.ip) with ip := b.ip + 1 } : DS VV MM) [vJ] := by
      intro y hy
      exact DS.set_env_ne _ _ (by simpa only [List.mem_singleton] using hy)
    exact ⟨⟨by simp only; rw [h1]; omega, h2, Cst.of_fr h3 hf (by decide),
      Fr.trans h4 (Fr.weaken hf (by simp))⟩,
      by rw [hf _ (by decide), hbi], by rw [hf _ (by decide), hbl]⟩
  · rintro b ⟨⟨h1, h2, h3, h4⟩, _, _⟩
    exact ⟨h1, h2, h3, h4⟩

end NearQuarticWires.StageRecovery
