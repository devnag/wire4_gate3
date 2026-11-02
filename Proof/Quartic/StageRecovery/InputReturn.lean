import Proof.Quartic.StageRecovery.ModLoopSuffix

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: the actual length of
the retained literal Formula token stream bounds the paid return pass. -/
def tokenLengthVar : Fin VV := ⟨106, by decide⟩
/-- `lem:print`, paper/paper.tex: the physical input
return counter does not alias any postfix, support or cache counter. -/
def inputReturnIndex : Fin VV := ⟨107, by decide⟩

/-- `lem:print`, paper/paper.tex: every input-head
return takes one actual backwards step for each consumed Formula bit. -/
def inputReturnProgram : St VV MM :=
  forS inputReturnIndex tokenLengthVar (.op .bkI)

/-- `lem:print`, paper/paper.tex: a paid return of the
original input head retains every actual output and store component. -/
def inputRest (a : DS VV MM) := formulaRest a

/-- `lem:print`, paper/paper.tex: the literal return
loop resets the Formula head in linear stream length, with all memory
contents, cache cursors and computed residues retained exactly. -/
theorem inputReturnProgram_spec (C : Ctx) (a : DS VV MM) (L base : ℕ)
    (hL : a.env tokenLengthVar = L) (hip : a.ip = base + L) (hfit : L < 2 ^ C.Wd) :
    Hs C inputReturnProgram a (5 * L + 4) (fun b =>
      b.ip = base ∧ inputRest b = inputRest a ∧ Fr a b [inputReturnIndex]) := by
  let I : ℕ → DS VV MM → Prop := fun k b =>
    b.ip = base + (L - k) ∧ inputRest b = inputRest a ∧ Fr a b [inputReturnIndex]
  unfold inputReturnProgram
  refine (forS_spec' (C := C) inputReturnIndex tokenLengthVar (by decide) (.op .bkI)
    a L hfit I 1 ?_ ⟨by simpa using hip, rfl, Fr.refl _ _⟩ hL ?_).mono (by omega) ?_
  · intro k b value ⟨h1, h2, h3⟩
    exact ⟨h1, h2, Fr.trans h3 (Fr.set _ _ (by decide))⟩
  · intro k hk b ⟨h1, h2, h3⟩ hbi hbl
    refine (Hs.op (OpEx.bkI b (by rw [h1]; omega)) rfl).mono le_rfl ?_
    rintro d rfl
    exact ⟨⟨by simp only; rw [h1]; omega, h2, h3⟩, hbi, hbl⟩
  · rintro b ⟨⟨h1, h2, h3⟩, _, _⟩
    exact ⟨by simpa using h1, h2, h3⟩

end NearQuarticWires.StageRecovery
