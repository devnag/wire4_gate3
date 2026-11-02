import Proof.Quartic.StageRecovery.MobSubset

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: the current reduced
coefficient in a sequential inclusion–exclusion sum. -/
def coefficientVar : Fin VV := ⟨95, by decide⟩
/-- `lem:print`, paper/paper.tex: the once-cached
modular formula value of the current support. -/
def sampledValueVar : Fin VV := ⟨96, by decide⟩
/-- `lem:print`, paper/paper.tex: the parity of the
outer support's degree in inclusion–exclusion. -/
def supportParityVar : Fin VV := ⟨97, by decide⟩
/-- `lem:print`, paper/paper.tex: the parity of the
cached support's degree in inclusion–exclusion. -/
def candidateParityVar : Fin VV := ⟨98, by decide⟩

/-- `lem:print`, paper/paper.tex: a finite signed
inclusion–exclusion update normalized modulo the actual modulus. -/
def signedMobStep (q : ℕ) (applies sameParity : Bool) (acc value : ℕ) : ℕ :=
  if applies then (acc + (if sameParity then value else (q - value) % q)) % q else acc

/-- `lem:print`, paper/paper.tex: the actual update
uses modular negation only for a negative sign and reduces its sum
immediately, retaining the cached value and inclusion-test metadata. -/
def signedMobProgram : St VV MM :=
  .ite (.eq subsetVar v1)
    (.seq (.op (.copy leftVar coefficientVar))
      (.seq (.op (.copy rightVar sampledValueVar))
        (.seq (.ite (.eq supportParityVar candidateParityVar) skipS (negateModProgram rightVar))
          (.seq addModProgram (.op (.copy coefficientVar leftVar)))))) skipS

/-- `lem:print`, paper/paper.tex: the finite arithmetic
work set of one actual signed coefficient update. -/
def signedMobScratch : List (Fin VV) :=
  [coefficientVar, leftVar, rightVar, productVar, quotientVar, remainderVar, vJ]

/-- `lem:print`, paper/paper.tex: one actual modular
inclusion–exclusion step handles either sign, including zero residues,
without any inverse or field assumption on the recovery modulus. -/
theorem signedMobProgram_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (q acc value : ℕ) (applies sameParity : Bool)
    (hq : 0 < q) (hqfit : 2 * q ≤ 2 ^ C.Wd)
    (haq : a.env modulusVar = q) (hacc : a.env coefficientVar = acc)
    (hvalue : a.env sampledValueVar = value) (hacclt : acc < q) (hvaluelt : value < q)
    (happly : a.env subsetVar = if applies then 1 else 0)
    (hparity : decide (a.env supportParityVar = a.env candidateParityVar) = sameParity) :
    Hs C signedMobProgram a 23 (fun b =>
      b.env coefficientVar = signedMobStep q applies sameParity acc value ∧
      b.sh = a.sh ∧ Cst b ∧ Fr a b signedMobScratch) := by
  unfold signedMobProgram
  refine (Hs.ite (c := .eq subsetVar v1) (show subsetVar ≠ v1 by decide) (fun he => ?_) (fun he => ?_)).mono
    (show 22 + 1 ≤ 23 by omega) (fun _ h => h)
  · have hap : applies = true := by
      revert he
      simp only [Cnd.eval, happly, hc.one]
      cases applies <;> simp
    subst applies
    refine Hs.seq (t2 := 20) (hs_copy C leftVar coefficientVar a (by decide)) fun b hb => ?_
    subst b
    refine Hs.seq (t2 := 18) (hs_copy C rightVar sampledValueVar _ (by decide)) fun b hb => ?_
    subst b
    let d := (a.set leftVar acc).set rightVar value
    have heqd : (a.set leftVar (a.env coefficientVar)).set rightVar
        ((a.set leftVar (a.env coefficientVar)).env sampledValueVar) = d := by
      simp (config := {decide := true}) [d, DS.set, hacc, hvalue]
    rw [heqd]
    have hdc : Cst d := Cst.of_fr (T := [leftVar, rightVar]) hc
      (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide))) (by decide)
    have hdq : d.env modulusVar = q := by simp (config := {decide := true}) [d, DS.set, haq]
    have hdp : decide (d.env supportParityVar = d.env candidateParityVar) = sameParity := by
      simpa (config := {decide := true}) [d, DS.set] using hparity
    have hsign : Hs C (.ite (.eq supportParityVar candidateParityVar) skipS (negateModProgram rightVar)) d 8
        (fun e => e.env rightVar = (if sameParity then value else (q - value) % q) ∧
          e.sh = d.sh ∧ Cst e ∧ Fr d e [rightVar, productVar, quotientVar, remainderVar, vJ]) := by
      refine Hs.ite (show supportParityVar ≠ candidateParityVar by decide) (fun he => ?_) (fun he => ?_)
      · have hs : sameParity = true := by simpa [Cnd.eval, hdp] using he
        refine (skip_spec d).mono (by omega) ?_
        rintro e rfl
        exact ⟨by simp (config := {decide := true}) [DS.set, d, hs], rfl,
          Cst.of_fr hdc (Fr.set _ _ (by decide : vJ ∈ [vJ])) (by decide), Fr.set _ _ (by decide)⟩
      · have hs : sameParity = false := by simpa [Cnd.eval, hdp] using he
        refine (negateModProgram_spec C d rightVar (by decide) (by rw [hdq]; exact hq)
          (by rw [hdq]; exact hqfit) (by simpa (config := {decide := true}) [d, DS.set, haq] using hvaluelt.le)).mono le_rfl ?_
        rintro e ⟨her, hesh, hef⟩
        exact ⟨by simpa (config := {decide := true}) [hs, hdq, d, DS.set, haq] using her,
          hesh, Cst.of_fr hdc hef (by decide), Fr.weaken hef (by decide)⟩
    refine (Hs.seq (t2 := 7) hsign fun e ⟨her, hesh, hec, hef⟩ => ?_).mono (by omega) (fun _ h => h)
    have hel : e.env leftVar = acc := by rw [hef _ (by decide)]; simp (config := {decide := true}) [d, DS.set]
    have heq : e.env modulusVar = q := by rw [hef _ (by decide), hdq]
    have hright : (if sameParity then value else (q - value) % q) < q := by
      cases sameParity <;> simp [Nat.mod_lt _ hq, hvaluelt]
    refine Hs.seq (t2 := 1) (addModProgram_spec C e (by rw [heq]; exact hq)
      (by rw [heq]; exact hqfit) (by rw [hel, her]; omega)) fun b ⟨hbl, hbsh, hbf⟩ => ?_
    refine (hs_copy C coefficientVar leftVar b (by decide)).mono le_rfl ?_
    rintro f rfl
    refine ⟨by simp only [DS.set_env_self, hbl, hel, her, heq, signedMobStep, if_true], ?_, ?_, ?_⟩
    · change b.sh = a.sh
      rw [hbsh, hesh]
      rfl
    · exact Cst.of_fr (Cst.of_fr hec hbf (by decide)) (Fr.set _ _ (by decide : coefficientVar ∈ [coefficientVar])) (by decide)
    · exact Fr.trans (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide)))
        (Fr.trans (Fr.weaken hef (by decide))
          (Fr.trans (Fr.weaken hbf (by decide)) (Fr.set _ _ (by decide))))
  · have hap : applies = false := by
      revert he
      simp only [Cnd.eval, happly, hc.one]
      cases applies <;> simp
    refine (skip_spec a).mono (by omega) ?_
    rintro b rfl
    exact ⟨by simpa (config := {decide := true}) [DS.set, signedMobStep, hap] using hacc,
      rfl, Cst.of_fr hc (Fr.set _ _ (by decide : vJ ∈ [vJ])) (by decide), Fr.set _ _ (by decide)⟩

end NearQuarticWires.StageRecovery
