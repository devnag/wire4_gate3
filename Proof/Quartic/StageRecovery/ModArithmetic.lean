import Proof.Quartic.StageRecovery.NaturalArithmetic

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: the first reduced
postfix arithmetic argument. -/
def leftVar : Fin VV := ⟨71, by decide⟩
/-- `lem:print`, paper/paper.tex: the second reduced
postfix arithmetic argument. -/
def rightVar : Fin VV := ⟨72, by decide⟩
/-- `lem:print`, paper/paper.tex: the bounded temporary
integer product before modular reduction. -/
def productVar : Fin VV := ⟨75, by decide⟩

/-- `lem:print`, paper/paper.tex: actual binary addition
is immediately followed by division by the recovery modulus. -/
def addModProgram : St VV MM :=
  .seq (.op (.add leftVar rightVar))
    (.seq (.op (.dm leftVar modulusVar quotientVar remainderVar))
      (.op (.copy leftVar remainderVar)))

/-- `lem:print`, paper/paper.tex: actual binary
multiplication is immediately reduced before the next formula node. -/
def multiplyModProgram : St VV MM :=
  .seq (.op (.mul leftVar rightVar productVar))
    (.seq (.op (.dm productVar modulusVar quotientVar remainderVar))
      (.op (.copy leftVar remainderVar)))

/-- `lem:print`, paper/paper.tex: the literal three
arithmetic instructions compute the reduced sum and retain both the
actual source cursors and the second operand. -/
theorem addModProgram_spec (C : Ctx) (a : DS VV MM)
    (hq : 0 < a.env modulusVar) (hqfit : 2 * a.env modulusVar ≤ 2 ^ C.Wd)
    (hfit : a.env leftVar + a.env rightVar < 2 ^ C.Wd) :
    Hs C addModProgram a 5 (fun b =>
      b.env leftVar = (a.env leftVar + a.env rightVar) % a.env modulusVar ∧
      b.sh = a.sh ∧ Fr a b [leftVar, quotientVar, remainderVar]) := by
  unfold addModProgram
  refine Hs.seq (t2 := 3) (hs_add C leftVar rightVar a (by decide) hfit) fun b hb => ?_
  subst b
  refine Hs.seq (t2 := 1) (hs_dm C leftVar modulusVar quotientVar remainderVar _
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simpa (config := {decide := true}) [DS.set] using hq)
    (by simpa (config := {decide := true}) [DS.set] using hqfit)) fun b hb => ?_
  subst b
  refine (hs_copy C leftVar remainderVar _ (by decide)).mono le_rfl ?_
  rintro b rfl
  refine ⟨by simp (config := {decide := true}) [DS.set], rfl, ?_⟩
  exact Fr.trans (Fr.set _ _ (by decide))
    (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide))))

/-- `lem:print`, paper/paper.tex: the literal binary
product and division compute the reduced product with no unreduced
formula value in the source or output codec. -/
theorem multiplyModProgram_spec (C : Ctx) (a : DS VV MM)
    (hq : 0 < a.env modulusVar) (hqfit : 2 * a.env modulusVar ≤ 2 ^ C.Wd)
    (hfit : a.env leftVar * a.env rightVar < 2 ^ C.Wd) :
    Hs C multiplyModProgram a 5 (fun b =>
      b.env leftVar = (a.env leftVar * a.env rightVar) % a.env modulusVar ∧
      b.sh = a.sh ∧ Fr a b [leftVar, productVar, quotientVar, remainderVar]) := by
  unfold multiplyModProgram
  refine Hs.seq (t2 := 3) (hs_mul C leftVar rightVar productVar a
    (by decide) (by decide) (by decide) hfit) fun b hb => ?_
  subst b
  refine Hs.seq (t2 := 1) (hs_dm C productVar modulusVar quotientVar remainderVar _
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simpa (config := {decide := true}) [DS.set] using hq)
    (by simpa (config := {decide := true}) [DS.set] using hqfit)) fun b hb => ?_
  subst b
  refine (hs_copy C leftVar remainderVar _ (by decide)).mono le_rfl ?_
  rintro b rfl
  refine ⟨by simp (config := {decide := true}) [DS.set], rfl, ?_⟩
  exact Fr.trans (Fr.set _ _ (by decide))
    (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide))))

end NearQuarticWires.StageRecovery
