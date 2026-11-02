import Proof.Gates.Cells.Run
import Proof.Gates.Cells.Kit
import Proof.Quartic.StageSolve.CenteredValue

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicGates.Close.Cells

/-- `lem:residue`, paper/paper.tex: the actual positive modulus. -/
def modulusVar : Fin VV := ⟨60, by decide⟩
/-- `lem:residue`, paper/paper.tex: the bounded native table value. -/
def magnitudeVar : Fin VV := ⟨61, by decide⟩
/-- `lem:residue`, paper/paper.tex: the division quotient. -/
def quotientVar : Fin VV := ⟨62, by decide⟩
/-- `lem:residue`, paper/paper.tex: the unsigned remainder. -/
def remainderVar : Fin VV := ⟨63, by decide⟩
/-- `lem:residue`, paper/paper.tex: the positive-endpoint cutoff. -/
def halfVar : Fin VV := ⟨64, by decide⟩
/-- `lem:residue`, paper/paper.tex: the exact output sign. -/
def signVar : Fin VV := ⟨65, by decide⟩

/-- `lem:residue`, paper/paper.tex: a fixed binary program
divides the nonnegative native value by the modulus and selects its
centered sign and magnitude, retaining the positive endpoint. -/
def centerNatural : St VV MM :=
  .seq (.op (.dm magnitudeVar modulusVar quotientVar remainderVar))
    (.seq (.op (.copy halfVar modulusVar))
      (.seq (.op (.half halfVar))
        (.ite (.lt halfVar remainderVar)
          (.seq (.op (.copy magnitudeVar modulusVar))
            (.seq (.op (.sub magnitudeVar remainderVar))
              (.seq (.op (.zero signVar)) (.op (.inc signVar)))))
          (.seq (.op (.copy magnitudeVar remainderVar)) (.op (.zero signVar))))))

/-- `lem:residue`, paper/paper.tex: the centered sign is
one exactly above half the modulus. -/
def naturalSign (q value : ℕ) : ℕ := if q / 2 < value % q then 1 else 0

/-- `lem:residue`, paper/paper.tex: the centered magnitude
is the remainder or its distance from the positive modulus. -/
def naturalMagnitude (q value : ℕ) : ℕ :=
  if q / 2 < value % q then q - value % q else value % q

/-- `lem:residue`, paper/paper.tex: the sign and magnitude
computed from an unsigned native table entry encode the exact centered
integer, including zero and even-modulus endpoints. -/
theorem naturalParts_eq (q value : ℕ) (hq : 0 < q) :
    NearCubicGates.Close.WordPrograms.SInt.sval (naturalMagnitude q value)
      (decide (naturalSign q value = 1)) = Walks.centeredResidue q value := by
  have h := StageSolve.centeredMagnitude_eq q value false
  simp only [NearCubicGates.Close.WordPrograms.SInt.sval, Bool.false_eq_true, if_false] at h
  rw [← h]
  simp only [StageSolve.centeredMagnitude, ne_of_gt hq, if_false,
    Bool.toNat_false, Nat.sub_zero, Bool.not_false]
  unfold naturalMagnitude naturalSign
  split_ifs <;> simp [NearCubicGates.Close.WordPrograms.SInt.sval]

/-- `lem:residue`, paper/paper.tex: the literal binary
division and centered branch execute within a constant number of
arithmetic operations, preserving all input, store and output cursors. -/
theorem centerNatural_spec (C : Ctx) (a : DS VV MM)
    (hq : 0 < a.env modulusVar) (hfit : 2 * a.env modulusVar ≤ 2 ^ C.Wd)
    (hW : 1 < 2 ^ C.Wd) :
    Hs C centerNatural a 20 (fun b =>
      b.env magnitudeVar = naturalMagnitude (a.env modulusVar) (a.env magnitudeVar) ∧
      b.env signVar = naturalSign (a.env modulusVar) (a.env magnitudeVar) ∧
      b.sh = a.sh ∧
      Fr a b [magnitudeVar, quotientVar, remainderVar, halfVar, signVar]) := by
  unfold centerNatural
  refine Hs.mono (Hs.seq (t2 := 12) (hs_dm C magnitudeVar modulusVar quotientVar remainderVar a
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hq hfit)
    (fun b hb => ?_)) (by omega) (fun _ h => h)
  subst b
  refine Hs.seq (t2 := 10) (hs_copy C halfVar modulusVar _ (by decide)) fun b hb => ?_
  subst b
  refine Hs.seq (t2 := 8) (hs_half C halfVar _) fun b hb => ?_
  subst b
  let base := (((a.set quotientVar (a.env magnitudeVar / a.env modulusVar)).set remainderVar
    (a.env magnitudeVar % a.env modulusVar)).set halfVar (a.env modulusVar)).set halfVar
      (a.env modulusVar / 2)
  change Hs C (.ite (.lt halfVar remainderVar) _ _) base _ _
  have hm : base.env modulusVar = a.env modulusVar := by
    simp (config := {decide := true}) [base, DS.set, modulusVar, quotientVar, remainderVar, halfVar]
  have hr : base.env remainderVar = a.env magnitudeVar % a.env modulusVar := by
    simp (config := {decide := true}) [base, DS.set, remainderVar, halfVar]
  have hh : base.env halfVar = a.env modulusVar / 2 := by simp [base]
  refine Hs.ite (show halfVar ≠ remainderVar by decide) (fun ht => ?_) (fun ht => ?_)
  · have hbranch : a.env modulusVar / 2 < a.env magnitudeVar % a.env modulusVar := by
      simpa [Cnd.eval, hh, hr] using ht
    refine Hs.seq (t2 := 5) (hs_copy C magnitudeVar modulusVar base (by decide)) fun b hb => ?_
    subst b
    refine Hs.seq (t2 := 3) (hs_sub C magnitudeVar remainderVar _ (by decide) (by
      simp (config := {decide := true}) [DS.set, magnitudeVar, remainderVar, hm, hr]
      exact Nat.le_of_lt (Nat.mod_lt _ hq))) fun b hb => ?_
    subst b
    refine Hs.seq (t2 := 1) (hs_zero C signVar _) fun b hb => ?_
    subst b
    refine Hs.mono (hs_inc C signVar _ (by simpa only [DS.set_env_self, zero_add] using hW)) le_rfl ?_
    rintro b rfl
    refine ⟨?_, ?_, rfl, ?_⟩
    · simp (config := {decide := true}) [naturalMagnitude, hbranch, DS.set, hm, hr]
    · simp [naturalSign, hbranch]
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      rcases hx with ⟨hmag, hquot, hrem, hhalf, hsign⟩
      simp only [base, DS.set, Function.update_of_ne hmag, Function.update_of_ne hquot,
        Function.update_of_ne hrem, Function.update_of_ne hhalf, Function.update_of_ne hsign]
  · have hbranch : ¬ a.env modulusVar / 2 < a.env magnitudeVar % a.env modulusVar := by
      simpa [Cnd.eval, hh, hr] using ht
    refine Hs.mono (Hs.seq (t2 := 1) (hs_copy C magnitudeVar remainderVar base (by decide))
      (fun b hb => ?_)) (by omega) (fun _ h => h)
    subst b
    refine Hs.mono (hs_zero C signVar _) le_rfl ?_
    rintro b rfl
    refine ⟨?_, ?_, rfl, ?_⟩
    · simp (config := {decide := true}) [naturalMagnitude, hbranch, DS.set, hr]
    · simp [naturalSign, hbranch]
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      rcases hx with ⟨hmag, hquot, hrem, hhalf, hsign⟩
      simp only [base, DS.set, Function.update_of_ne hmag, Function.update_of_ne hquot,
        Function.update_of_ne hrem, Function.update_of_ne hhalf, Function.update_of_ne hsign]

end NearQuarticWires.StageRecovery
