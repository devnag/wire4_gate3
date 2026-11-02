import Proof.Quartic.StageRecovery.FamilySetup

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: the seven scalar
setup fields are read from initialized zero, one, radix and mask words. -/
def familyScalarVars : List (Fin VV) :=
  [vZ, vZ, vZ, v1, coordinateBaseVar, vZ, familyMaskVar]

/-- `lem:print`, paper/paper.tex: all eleven native
family setup fields are physically serialized, including the two unary
dimensions and two empty working streams. -/
def familyFieldsProgram : St VV MM :=
  .seq (FixedBits.emitFields familyScalarVars)
    (.seq (FixedBits.emitUnaryFrom arityVar)
      (.seq (FixedBits.emitUnaryFrom familyBoundVar) (StageLift.emitLiteral [false, false])))

/-- `lem:print`, paper/paper.tex: the literal complete
native family input is constructed from actual source registers rather
than supplied finite setup tapes. -/
theorem familyFieldsProgram_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (r : FamilyRequest) (hV : a.env arityVar = r.arity) (hD : a.env familyBoundVar = r.degree)
    (hwidth : a.env FixedBits.width = r.width)
    (hbase : a.env coordinateBaseVar = 2 ^ r.arity)
    (hmask : a.env familyMaskVar = 2 ^ r.arity - 1)
    (hfit : r.width < 2 ^ C.Wd) (hW : 2 ≤ C.Wd) :
    Hs C familyFieldsProgram a (1000 * (r.width + r.arity + r.degree + 1)) (fun b =>
      b.out = a.out ++ r.word ∧ FixedBits.outputRest b = FixedBits.outputRest a ∧
      Cst b ∧ Fr a b FixedBits.fieldScratch) := by
  have hVfit : r.arity < 2 ^ C.Wd := by unfold FamilyRequest.width at hfit; omega
  have hDfit : r.degree < 2 ^ C.Wd := by unfold FamilyRequest.width at hfit; omega
  unfold familyFieldsProgram
  refine Hx.hs (Hs.then (FixedBits.emitFields_spec C familyScalarVars a hc (by decide)
    r.width hwidth hfit hW) fun b ⟨hbo, hbr, hbw, hbc, hbf⟩ n1 hn1 => ?_)
  have hbV : b.env arityVar = r.arity := by rw [hbf _ (by decide), hV]
  refine Hs.then (FixedBits.emitUnaryFrom_spec C b hbc arityVar (by decide) (by decide)
    r.arity hbV hVfit) fun d ⟨hdo, hdr, hdc, hdf⟩ n2 hn2 => ?_
  have hdD : d.env familyBoundVar = r.degree := by rw [hdf _ (by decide), hbf _ (by decide), hD]
  refine Hs.then (FixedBits.emitUnaryFrom_spec C d hdc familyBoundVar (by decide) (by decide)
    r.degree hdD hDfit) fun e ⟨heo, her, hec, hef⟩ n3 hn3 => ?_
  refine Hs.last (StageLift.emitLiteral_spec C [false, false] e hec)
    fun f ⟨hfo, hfr, hfc, hff⟩ n4 hn4 => ?_
  refine ⟨⟨?_, hfr.trans (her.trans (hdr.trans hbr)), hfc, ?_⟩, ?_⟩
  · rw [hfo, heo, hdo, hbo]
    simp [familyScalarVars, hc.z, hc.one, hbase, hmask, FamilyRequest.word,
      FamilyRequest.fields, Top.loadRec, List.append_assoc]
    rfl
  · exact Fr.trans hbf (Fr.trans (Fr.weaken hdf (by decide))
      (Fr.trans (Fr.weaken hef (by decide)) (Fr.weaken hff (by decide))))
  · simp only [familyScalarVars, List.length_cons, List.length_nil] at hn1
    simp only [List.length_cons, List.length_nil] at hn4
    omega

end NearQuarticWires.StageRecovery
