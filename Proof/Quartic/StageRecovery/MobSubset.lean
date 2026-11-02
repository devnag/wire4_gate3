import Proof.Quartic.StageRecovery.ModPointFields

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicGates.Close.Cells NearCubicGates.Close.Expand

attribute [local instance] Classical.propDecidable

/-- `lem:print`, paper/paper.tex: the outer support in
one sequential coefficient accumulation. -/
def supportVar : Fin VV := ⟨85, by decide⟩
/-- `lem:print`, paper/paper.tex: the cached support
whose modular point value is currently being inspected. -/
def candidateVar : Fin VV := ⟨86, by decide⟩
/-- `lem:print`, paper/paper.tex: the Boolean result of
the paid characteristic-set inclusion test. -/
def subsetVar : Fin VV := ⟨87, by decide⟩
/-- `lem:print`, paper/paper.tex: work copies and the
bounded loop counter for characteristic-set inclusion. -/
def subsetLeft : Fin VV := ⟨88, by decide⟩
/-- `lem:print`, paper/paper.tex: the shifted cached
characteristic set in the inclusion test. -/
def subsetRight : Fin VV := ⟨89, by decide⟩
/-- `lem:print`, paper/paper.tex: the number of support
coordinates physically compared so far. -/
def subsetIndex : Fin VV := ⟨90, by decide⟩
/-- `lem:print`, paper/paper.tex: the current outer
support bit after binary division. -/
def subsetLeftBit : Fin VV := ⟨91, by decide⟩
/-- `lem:print`, paper/paper.tex: the current cached
support bit after binary division. -/
def subsetRightBit : Fin VV := ⟨92, by decide⟩
/-- `lem:print`, paper/paper.tex: the next shifted outer
support after binary division. -/
def subsetLeftNext : Fin VV := ⟨93, by decide⟩
/-- `lem:print`, paper/paper.tex: the next shifted
cached support after binary division. -/
def subsetRightNext : Fin VV := ⟨94, by decide⟩

/-- `lem:print`, paper/paper.tex: inclusion of the
first `k` characteristic bits, expressed without indexed table access. -/
def bitSubset (k s t : ℕ) : Prop := ∀ j < k, t / 2 ^ j % 2 ≤ s / 2 ^ j % 2

/-- `lem:print`, paper/paper.tex: one additional binary
comparison extends precisely the already checked support prefix. -/
theorem bitSubset_succ (k s t : ℕ) :
    bitSubset (k + 1) s t ↔ bitSubset k s t ∧ t / 2 ^ k % 2 ≤ s / 2 ^ k % 2 := by
  constructor
  · intro h
    exact ⟨fun j hj => h j (by omega), h k (by omega)⟩
  · rintro ⟨h, hk⟩ j hj
    by_cases he : j = k
    · simpa [he] using hk
    · exact h j (by omega)

/-- `lem:print`, paper/paper.tex: the finite binary
inclusion predicate is exactly inclusion of the original atom supports. -/
theorem bitSubset_eq (V s t : ℕ) : bitSubset V s t ↔ setOf V t ⊆ setOf V s := by
  constructor
  · intro h j hj
    simp only [NearCubicGates.Close.Expand.setOf, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    rw [Nat.testBit_eq_decide_div_mod_eq] at hj ⊢
    have ht : t / 2 ^ j.val % 2 = 1 := by simpa using hj
    have := h j.val j.isLt
    have := Nat.mod_lt (s / 2 ^ j.val) (by decide : 0 < 2)
    simp only [decide_eq_true_eq]
    omega
  · intro h j hj
    have hh := @h ⟨j, hj⟩
    simp only [NearCubicGates.Close.Expand.setOf, Finset.mem_filter, Finset.mem_univ, true_and,
      Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq] at hh
    have := Nat.mod_lt (t / 2 ^ j) (by decide : 0 < 2)
    have := Nat.mod_lt (s / 2 ^ j) (by decide : 0 < 2)
    by_cases ht : t / 2 ^ j % 2 = 1
    · have hs := hh ht
      omega
    · omega

/-- `lem:print`, paper/paper.tex: every support bit is
read by two actual binary divisions, with a persistent Boolean result. -/
def subsetBitProgram : St VV MM :=
  .seq (.op (.dm subsetLeft v2 subsetLeftNext subsetLeftBit))
    (.seq (.op (.dm subsetRight v2 subsetRightNext subsetRightBit))
      (.seq (.ite (.lt subsetLeftBit subsetRightBit) (.op (.zero subsetVar)) skipS)
        (.seq (.op (.copy subsetLeft subsetLeftNext))
          (.op (.copy subsetRight subsetRightNext)))))

/-- `lem:print`, paper/paper.tex: actual sequential
halving inspects exactly the original arity, with no random access. -/
def subsetProgram : St VV MM :=
  .seq (.op (.copy subsetLeft supportVar))
    (.seq (.op (.copy subsetRight candidateVar))
      (.seq (.op (.copy subsetVar v1)) (forS subsetIndex arityVar subsetBitProgram)))

/-- `lem:print`, paper/paper.tex: the characteristic
inclusion loop modifies only its declared finite work registers. -/
def subsetScratch : List (Fin VV) :=
  [subsetVar, subsetLeft, subsetRight, subsetIndex, subsetLeftBit, subsetRightBit,
    subsetLeftNext, subsetRightNext, vJ]

/-- `lem:print`, paper/paper.tex: a single bit comparison
retains the outer inclusion-loop counter. -/
def subsetBitScratch : List (Fin VV) :=
  [subsetVar, subsetLeft, subsetRight, subsetLeftBit, subsetRightBit,
    subsetLeftNext, subsetRightNext, vJ]

/-- `lem:print`, paper/paper.tex: each literal support
comparison advances both work words and updates the exact prefix result. -/
theorem subsetBitProgram_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (s t k : ℕ) (hleft : a.env subsetLeft = s / 2 ^ k)
    (hright : a.env subsetRight = t / 2 ^ k)
    (hsubset : a.env subsetVar = if bitSubset k s t then 1 else 0)
    (hW : 2 ≤ C.Wd) :
    Hs C subsetBitProgram a 11 (fun b =>
      b.env subsetLeft = s / 2 ^ (k + 1) ∧
      b.env subsetRight = t / 2 ^ (k + 1) ∧
      b.env subsetVar = (if bitSubset (k + 1) s t then 1 else 0) ∧
      b.sh = a.sh ∧ Fr a b subsetBitScratch) := by
  have h4 : 4 ≤ 2 ^ C.Wd := by
    exact (show 4 = 2 ^ 2 by norm_num).le.trans
      (Nat.pow_le_pow_right (by decide) hW)
  unfold subsetBitProgram
  refine Hs.seq (t2 := 9) (hs_dm C subsetLeft v2 subsetLeftNext subsetLeftBit a
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [hc.two]; omega) (by rw [hc.two]; omega)) fun b hb => ?_
  subst b
  refine Hs.seq (t2 := 7) (hs_dm C subsetRight v2 subsetRightNext subsetRightBit _
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simpa (config := {decide := true}) [DS.set] using (show 0 < a.env v2 by rw [hc.two]; omega))
    (by simpa (config := {decide := true}) [DS.set] using (show 2 * a.env v2 ≤ 2 ^ C.Wd by rw [hc.two]; omega))) fun b hb => ?_
  subst b
  let d := ((a.set subsetLeftNext (a.env subsetLeft / a.env v2)).set subsetLeftBit
    (a.env subsetLeft % a.env v2)).set subsetRightNext (a.env subsetRight / a.env v2) |>.set
      subsetRightBit (a.env subsetRight % a.env v2)
  have hdleft : d.env subsetLeftNext = s / 2 ^ k / 2 := by
    simp (config := {decide := true}) [d, DS.set, hleft, hc.two]
  have hdright : d.env subsetRightNext = t / 2 ^ k / 2 := by
    simp (config := {decide := true}) [d, DS.set, hright, hc.two]
  have hdsubset : d.env subsetVar = if bitSubset k s t then 1 else 0 := by
    simpa (config := {decide := true}) [d, DS.set] using hsubset
  have hdlb : d.env subsetLeftBit = s / 2 ^ k % 2 := by
    simp (config := {decide := true}) [d, DS.set, hleft, hc.two]
  have hdrb : d.env subsetRightBit = t / 2 ^ k % 2 := by
    simp (config := {decide := true}) [d, DS.set, hright, hc.two]
  have hdf : Fr a d subsetBitScratch := by
    exact Fr.trans (Fr.set _ _ (by decide))
      (Fr.trans (Fr.set _ _ (by decide))
        (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide))))
  change Hs C (.seq (.ite (.lt subsetLeftBit subsetRightBit)
    (.op (.zero subsetVar)) skipS) (.seq (.op (.copy subsetLeft subsetLeftNext))
      (.op (.copy subsetRight subsetRightNext)))) d 7 _
  have hp : Hs C (.ite (.lt subsetLeftBit subsetRightBit) (.op (.zero subsetVar)) skipS) d 2
      (fun e => e.env subsetVar = (if bitSubset (k + 1) s t then 1 else 0) ∧
        e.sh = d.sh ∧ Fr d e [subsetVar, vJ]) := by
    refine Hs.ite (show subsetLeftBit ≠ subsetRightBit by decide) (fun he => ?_) (fun he => ?_)
    · have hbad : ¬ t / 2 ^ k % 2 ≤ s / 2 ^ k % 2 := by
        simpa [Cnd.eval, hdlb, hdrb] using he
      refine (hs_zero C subsetVar d).mono le_rfl ?_
      rintro e rfl
      exact ⟨by simp [bitSubset_succ, hbad], rfl, Fr.set _ _ (by decide)⟩
    · have hgood : t / 2 ^ k % 2 ≤ s / 2 ^ k % 2 := by
        have : ¬ s / 2 ^ k % 2 < t / 2 ^ k % 2 := by simpa [Cnd.eval, hdlb, hdrb] using he
        omega
      refine (skip_spec d).mono le_rfl ?_
      rintro e rfl
      exact ⟨by simpa (config := {decide := true}) [DS.set, bitSubset_succ, hgood] using hdsubset, rfl, Fr.set _ _ (by decide)⟩
  refine (Hs.seq (t2 := 3) hp fun e ⟨hes, hesh, hef⟩ => ?_).mono (by omega) (fun _ h => h)
  refine Hs.seq (t2 := 1) (hs_copy C subsetLeft subsetLeftNext e (by decide)) fun b hb => ?_
  subst b
  refine (hs_copy C subsetRight subsetRightNext _ (by decide)).mono le_rfl ?_
  rintro b rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [DS.set_env_ne _ _ (by decide : subsetLeft ≠ subsetRight), DS.set_env_self]
    rw [hef _ (by decide), hdleft, Nat.div_div_eq_div_mul, ← pow_succ]
  · simp only [DS.set_env_self, DS.set_env_ne _ _ (by decide : subsetRightNext ≠ subsetLeft)]
    rw [hef _ (by decide), hdright, Nat.div_div_eq_div_mul, ← pow_succ]
  · simpa (config := {decide := true}) [DS.set] using hes
  · change e.sh = a.sh
    rw [hesh]
    rfl
  · exact Fr.trans hdf (Fr.trans (Fr.weaken hef (by decide))
      (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide))))

/-- `lem:print`, paper/paper.tex: the complete paid
inclusion test returns the exact original support predicate in linear
arity many binary operations, preserving every store and source cursor. -/
theorem subsetProgram_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (V s t : ℕ) (hV : a.env arityVar = V) (hs : a.env supportVar = s)
    (ht : a.env candidateVar = t) (hfit : V < 2 ^ C.Wd) (hW : 2 ≤ C.Wd) :
    Hs C subsetProgram a (15 * V + 10) (fun b =>
      b.env subsetVar = (if setOf V t ⊆ setOf V s then 1 else 0) ∧
      b.sh = a.sh ∧ Cst b ∧ Fr a b subsetScratch) := by
  unfold subsetProgram
  refine (Hs.seq (t2 := 15 * V + 8) (hs_copy C subsetLeft supportVar a (by decide)) fun b hb => ?_).mono (by omega) (fun _ h => h)
  subst b
  refine (Hs.seq (t2 := 15 * V + 6) (hs_copy C subsetRight candidateVar _ (by decide)) fun b hb => ?_).mono (by omega) (fun _ h => h)
  subst b
  refine (Hs.seq (t2 := 15 * V + 4) (hs_copy C subsetVar v1 _ (by decide)) fun b hb => ?_).mono (by omega) (fun _ h => h)
  subst b
  let start := ((a.set subsetLeft s).set subsetRight t).set subsetVar 1
  let I : ℕ → DS VV MM → Prop := fun k b =>
    b.env subsetLeft = s / 2 ^ k ∧ b.env subsetRight = t / 2 ^ k ∧
    b.env subsetVar = (if bitSubset k s t then 1 else 0) ∧
    b.sh = a.sh ∧ Cst b ∧ Fr a b subsetScratch
  have he : (((a.set subsetLeft (a.env supportVar)).set subsetRight
      ((a.set subsetLeft (a.env supportVar)).env candidateVar)).set subsetVar
        (((a.set subsetLeft (a.env supportVar)).set subsetRight
          ((a.set subsetLeft (a.env supportVar)).env candidateVar)).env v1)) = start := by
    simp (config := {decide := true}) [start, DS.set, hs, ht, hc.one]
  rw [he]
  have hstart : I 0 start := by
    refine ⟨by simp (config := {decide := true}) [start, DS.set],
      by simp (config := {decide := true}) [start, DS.set],
      by simp (config := {decide := true}) [start, DS.set, bitSubset], rfl, ?_, ?_⟩
    · exact Cst.of_fr (T := subsetScratch) hc (Fr.trans (Fr.set _ _ (by decide))
        (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide)))) (by decide)
    · exact Fr.trans (Fr.set _ _ (by decide))
        (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide)))
  refine (forS_spec' (C := C) subsetIndex arityVar (by decide) subsetBitProgram start V hfit I 11
    (fun k b value ⟨h1, h2, h3, h4, h5, h6⟩ =>
      ⟨by simpa (config := {decide := true}) [DS.set] using h1,
        by simpa (config := {decide := true}) [DS.set] using h2,
        by simpa (config := {decide := true}) [DS.set] using h3, by simpa using h4,
        Cst.of_fr (T := [subsetIndex]) h5 (Fr.set _ _ (by decide)) (by decide),
        Fr.trans h6 (Fr.set _ _ (by decide))⟩) hstart
    (by simp (config := {decide := true}) [start, DS.set, hV]) ?_).mono (by omega) ?_
  · intro k hk b ⟨h1, h2, h3, h4, h5, h6⟩ hbi hba
    refine (subsetBitProgram_spec C b h5 s t k h1 h2 h3 hW).mono le_rfl ?_
    rintro d ⟨hd1, hd2, hd3, hd4, hd5⟩
    exact ⟨⟨hd1, hd2, hd3, hd4.trans h4, Cst.of_fr h5 hd5 (by decide), Fr.trans h6 (Fr.weaken hd5 (by decide))⟩,
      by rw [hd5 _ (by decide)]; exact hbi, by rw [hd5 _ (by decide)]; exact hba⟩
  · rintro b ⟨⟨_, _, hb3, hb4, hb5, hb6⟩, _, _⟩
    exact ⟨by simpa only [bitSubset_eq] using hb3, hb4, hb5, hb6⟩

end NearQuarticWires.StageRecovery
