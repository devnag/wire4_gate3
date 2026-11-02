import Proof.Quartic.StageRecovery.MobOuter

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: assigning a loop
counter does not change the aligned finite caches or output records. -/
theorem MobOuterAt.set {q V : ℕ} {entries : List CachedValue} {k : ℕ} {a : DS VV MM}
    (h : MobOuterAt q V entries k a) (x : Fin VV) (value : ℕ) :
    MobOuterAt q V entries k (a.set x value) := by
  obtain ⟨j, hj, hc⟩ := h.cached
  exact ⟨⟨j, hj, ⟨hc.supports, hc.parities, hc.values,
      hc.supportCursor, hc.parityCursor, hc.valueCursor⟩⟩,
    h.supports, h.parities, h.coefficients, h.supportCursor, h.parityCursor, h.coefficientCursor⟩

/-- `lem:print`, paper/paper.tex: the actual double
sequential driver computes all bounded-support coefficients from the
once-cached point values, paying every inner scan and rewind. -/
def coefficientDriverProgram : St VV MM :=
  forS outerIndexVar cacheCountVar coefficientOuterProgram

/-- `lem:print`, paper/paper.tex: the driver retains
its original arity, modulus, family length and all formula registers. -/
def coefficientDriverScratch : List (Fin VV) := outerIndexVar :: coefficientOuterScratch

/-- `prop:time`, paper/paper.tex: the literal driver
clock contains two factors of family length and only a linear arity
factor; no indexed-access or free-rewind convention is used. -/
def coefficientDriverCost (V N : ℕ) : ℕ := N * (N * (15 * V + 48) + 22) + 4

/-- `lem:print`, paper/paper.tex: one actual finite
program writes every coefficient exactly once in family order, using
the same cached values for every original support. -/
theorem coefficientDriverProgram_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (q V : ℕ) (entries : List CachedValue) (ha : MobOuterAt q V entries 0 a)
    (hV : a.env arityVar = V) (hq : a.env modulusVar = q)
    (hqlt : 0 < q) (hqfit : 2 * q ≤ 2 ^ C.Wd) (hvalues : ∀ e ∈ entries, e.2.2 < q)
    (hVfit : V < 2 ^ C.Wd) (hW : 2 ≤ C.Wd)
    (hcount : a.env cacheCountVar = entries.length) (hcountfit : entries.length < 2 ^ C.Wd) :
    Hs C coefficientDriverProgram a (coefficientDriverCost V entries.length) (fun b =>
      b.ram coefficientStore = cachedCoefficients q V entries ∧
      MobOuterAt q V entries entries.length b ∧ Cst b ∧ Fr a b coefficientDriverScratch ∧ b.out = a.out) := by
  let I : ℕ → DS VV MM → Prop := fun k b =>
    MobOuterAt q V entries k b ∧ Cst b ∧ Fr a b coefficientDriverScratch ∧ b.out = a.out
  unfold coefficientDriverProgram coefficientDriverCost
  refine (forS_spec' (C := C) outerIndexVar cacheCountVar (by decide) coefficientOuterProgram
    a entries.length hcountfit I (entries.length * (15 * V + 48) + 18) ?_
    ⟨ha, hc, Fr.refl _ _, rfl⟩ hcount ?_).mono (by simp) ?_
  · intro k b value ⟨h1, h2, h3, h4⟩
    exact ⟨h1.set _ _, Cst.of_fr (T := [outerIndexVar]) h2 (Fr.set _ _ (by decide)) (by decide),
      Fr.trans h3 (Fr.set _ _ (by simp [coefficientDriverScratch])), h4⟩
  · intro k hk b ⟨h1, h2, h3, h4⟩ hbi hbn
    refine (coefficientOuterProgram_spec C b h2 q V entries k hk h1
      (by rw [h3 _ (by decide), hV]) (by rw [h3 _ (by decide), hq])
      hqlt hqfit hvalues hVfit hW hbn hcountfit).mono le_rfl ?_
    rintro d ⟨hd1, hd2, hd3, hd4⟩
    exact ⟨⟨hd1, hd2, Fr.trans h3 (Fr.weaken hd3 (by intro y hy; simp [coefficientDriverScratch, hy])), hd4.trans h4⟩,
      by rw [hd3 _ (by decide), hbi], by rw [hd3 _ (by decide), hbn]⟩
  · rintro b ⟨⟨h1, h2, h3, h4⟩, _, _⟩
    refine ⟨?_, h1, h2, h3, h4⟩
    rw [h1.coefficients]
    apply List.take_of_length_le
    simp [cachedCoefficients]

/-- `prop:time`, paper/paper.tex: all physical cache
scans, writes and rewinds fit the sharp quadratic-family budget. -/
theorem coefficientDriverCost_le (V N : ℕ) :
    coefficientDriverCost V N ≤ 100 * (N + 1) ^ 2 * (V + 1) := by
  unfold coefficientDriverCost
  rw [Nat.pow_two]
  nlinarith [show 0 ≤ N * N * V by positivity]

end NearQuarticWires.StageRecovery
