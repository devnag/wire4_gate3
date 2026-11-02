import Proof.Quartic.StageRecovery.ModPayloads

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: one of the seven
literal postfix operations is selected by the decoded tag. -/
def tokenDispatch : List (St VV MM) → St VV MM
  | [] => skipS
  | handler :: handlers =>
      .ite (.eq tagVar vZ) handler
        (.seq (.op (.sub tagVar v1)) (tokenDispatch handlers))

/-- `lem:print`, paper/paper.tex: exact bounded tag
dispatch runs the selected physical token body and charges every test
and decrement; tags do not encode an additional arithmetic oracle. -/
theorem tokenDispatch_spec (C : Ctx) (handlers : List (St VV MM))
    (index : ℕ) (hi : index < handlers.length) (a : DS VV MM) (hc : Cst a)
    (htag : a.env tagVar = index) (cost : ℕ) (post : DS VV MM → Prop)
    (hhandler : Hs C handlers[index] (a.set tagVar 0) cost post) :
    Hs C (tokenDispatch handlers) a (cost + 3 * index + 1) post := by
  induction handlers generalizing index a with
  | nil => simp at hi
  | cons handler handlers ih =>
      cases index with
      | zero =>
          have he : (Cnd.eq tagVar vZ).eval a = true := by simp [Cnd.eval, htag, hc.z]
          have heq : a.set tagVar 0 = a := by
            cases a
            simp only [DS.set]
            congr
            exact Function.update_eq_self_iff.mpr htag.symm
          rw [heq] at hhandler
          exact Hs.iteT (c := .eq tagVar vZ) (show tagVar ≠ vZ by decide) he hhandler
      | succ index =>
          have he : (Cnd.eq tagVar vZ).eval a = false := by simp [Cnd.eval, htag, hc.z]
          refine (Hs.iteF (c := .eq tagVar vZ) (show tagVar ≠ vZ by decide) he
            (Hs.seq (t2 := cost + 3 * index + 1) (hs_sub C tagVar v1 a (by decide)
              (by rw [htag, hc.one]; omega)) fun b hb => ?_)).mono (by omega) (fun _ h => h)
          subst b
          have hbc : Cst (a.set tagVar (a.env tagVar - a.env v1)) :=
            Cst.of_fr (T := [tagVar]) hc (Fr.set _ _ (by decide)) (by decide)
          apply ih index (by simp at hi; omega) _ hbc
          · simp [htag, hc.one]
          · simpa only [List.getElem_cons_succ, DS.set, Function.update_idem] using hhandler

/-- `lem:print`, paper/paper.tex: literal token bodies
retain the original constant, variable, addition, negation, subtraction,
multiplication and power order of the formula codec. -/
def modularHandlers : List (St VV MM) :=
  [constantModHandler, variableModHandler, binaryModHandler false,
    unaryModHandler false, subtractionModHandler, binaryModHandler true, powerPayloadHandler]

/-- `lem:print`, paper/paper.tex: the complete physical
token operation parses the original tag and executes its selected body. -/
def modularToken : St VV MM := .seq (readVariable tagVar) (tokenDispatch modularHandlers)

end NearQuarticWires.StageRecovery
