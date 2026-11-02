import Proof.Quartic.StageRecovery.CacheBuildStep

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicGates.Close.Cells NearCubicGates.Close.Expand NearCubicGates.Close.Tabulator
open NearCubicGates.Close.Interfaces.Formats

/-- `lem:print`, paper/paper.tex: the family-cache
constructor uses a separate counter from both coefficient scans. -/
def cacheBuildIndex : Fin VV := ⟨112, by decide⟩

/-- `lem:print`, paper/paper.tex: the actual first pass
evaluates each original generated support once and writes its cache. -/
def buildCacheProgram : St VV MM := forS cacheBuildIndex cacheCountVar buildCachePointProgram

/-- `lem:print`, paper/paper.tex: the finite work frame
of cache construction retains the original Formula's request metadata. -/
def buildCacheScratch : List (Fin VV) := cacheBuildIndex :: buildCachePointScratch

/-- `lem:print`, paper/paper.tex: the complete actual
cache constructor performs one Formula evaluation and one paid input
return per support, retaining the literal coefficient-output store. -/
theorem buildCacheProgram_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    {V : ℕ} (F : Formula V) (q : ℕ) (points : List (ℕ × ℕ))
    (hprefix : CachePrefix (pointEntries q F points) 0 a)
    (hrecords : a.ram familyRecordStore = points.map (packedFamilyRecord V))
    (hcursor : a.rc familyRecordStore = 0) (hbase : a.env coordinateBaseVar = 2 ^ V)
    (hpoints : ∀ p ∈ points, p.1 < 2 ^ V) (hq : 2 ≤ q) (haq : a.env modulusVar = q)
    (hcount : a.env tokenCountVar = (toks F).length) (hcountfit : (toks F).length < 2 ^ C.Wd)
    (suffix : List Bool) (hin : C.inp.drop a.ip = tokenStream (toks F) ++ suffix)
    (hwidth : formulaTokenBound F + 5 ≤ C.Wd) (hVwidth : V + 2 ≤ C.Wd)
    (hdepth : q ^ ((toks F).length + 3) ≤ 2 ^ C.Wd)
    (hlength : a.env tokenLengthVar = (tokenStream (toks F)).length)
    (hlengthfit : (tokenStream (toks F)).length < 2 ^ C.Wd)
    (hfamilyCount : a.env cacheCountVar = points.length) (hfamilyFit : points.length < 2 ^ C.Wd) :
    Hs C buildCacheProgram a (points.length * (cachedEvaluationCost F + 20) + 4) (fun b =>
      CachePrefix (pointEntries q F points) points.length b ∧
      b.ram familyRecordStore = a.ram familyRecordStore ∧ b.rc familyRecordStore = points.length ∧
      b.ram coefficientStore = a.ram coefficientStore ∧ b.rc coefficientStore = a.rc coefficientStore ∧
      b.ip = a.ip ∧ Cst b ∧ Fr a b buildCacheScratch ∧ b.out = a.out) := by
  let I : ℕ → DS VV MM → Prop := fun k b =>
    CachePrefix (pointEntries q F points) k b ∧
    b.ram familyRecordStore = a.ram familyRecordStore ∧ b.rc familyRecordStore = k ∧
    b.ram coefficientStore = a.ram coefficientStore ∧ b.rc coefficientStore = a.rc coefficientStore ∧
    b.ip = a.ip ∧ Cst b ∧ Fr a b buildCacheScratch ∧ b.out = a.out
  unfold buildCacheProgram
  refine (forS_spec' (C := C) cacheBuildIndex cacheCountVar (by decide) buildCachePointProgram
    a points.length hfamilyFit I (cachedEvaluationCost F + 16) ?_
    ⟨hprefix, rfl, hcursor, rfl, rfl, rfl, hc, Fr.refl _ _, rfl⟩ hfamilyCount ?_).mono (by simp) ?_
  · intro k b value ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    exact ⟨h1.of_sh rfl, h2, h3, h4, h5, h6,
      Cst.of_fr (T := [cacheBuildIndex]) h7 (Fr.set _ _ (by decide)) (by decide),
      Fr.trans h8 (Fr.set _ _ (by simp [buildCacheScratch])), h9⟩
  · intro k hk b ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ hbi hbn
    refine (buildCachePointProgram_spec C b h7 F q points k hk h1
      (h2.trans hrecords) h3 (by rw [h8 _ (by decide), hbase]) hpoints hq
      (by rw [h8 _ (by decide), haq]) (by rw [h8 _ (by decide), hcount]) hcountfit suffix
      (by rw [h6]; exact hin) hwidth hVwidth hdepth
      (by rw [h8 _ (by decide), hlength]) hlengthfit).mono le_rfl ?_
    rintro d ⟨hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9⟩
    exact ⟨⟨hd1, hd2.trans h2, hd3, hd4.trans h4, hd5.trans h5, hd6.trans h6, hd7,
      Fr.trans h8 (Fr.weaken hd8 (by intro y hy; simp [buildCacheScratch, hy])), hd9.trans h9⟩,
      by rw [hd8 _ (by decide), hbi], by rw [hd8 _ (by decide), hbn]⟩
  · rintro b ⟨hb, _, _⟩
    exact hb

/-- `lem:print`, paper/paper.tex: the two outer metadata
streams are genuinely rewound once after cache construction. -/
def prepareCoefficientProgram : St VV MM :=
  .seq (.op (.rwM outerSupports)) (.op (.rwM outerParities))

/-- `lem:print`, paper/paper.tex: the exact state after
paying the outer metadata head returns. -/
def prepareCoefficient (a : DS VV MM) : DS VV MM :=
  (a.rew outerSupports).rew outerParities

/-- `lem:print`, paper/paper.tex: outer-head preparation
pays every traversed metadata record and preserves all other components. -/
theorem prepareCoefficientProgram_spec (C : Ctx) (a : DS VV MM) (N : ℕ)
    (hs : a.rc outerSupports = N) (hp : a.rc outerParities = N) :
    Hs C prepareCoefficientProgram a (2 * N + 3) (fun b => b = prepareCoefficient a) := by
  unfold prepareCoefficientProgram
  refine (Hs.seq (t1 := N + 1) (t2 := N + 1) ((hs_rwM C outerSupports a).mono
    (by rw [hs]) (fun _ h => h)) fun b hb => ?_).mono (by omega) (fun _ h => h)
  subst b
  exact (hs_rwM C outerParities _).mono
    (by simpa (config := {decide := true}) [DS.rew] using hp.le) (fun _ h => h)

/-- `lem:print`, paper/paper.tex: a completely built
cache and paid outer rewinds give the genuine start invariant for the
quadratic coefficient driver, with no supplied polynomial values. -/
theorem CachePrefix.driverReady {q V : ℕ} {entries : List CachedValue} {a : DS VV MM}
    (h : CachePrefix entries entries.length a) (hout : a.ram coefficientStore = [])
    (hcursor : a.rc coefficientStore = 0) : MobOuterAt q V entries 0 (prepareCoefficient a) := by
  have hc : ∀ m ∈ [cacheSupports, cacheParities, cacheValues, outerSupports, outerParities],
      a.rc m = entries.length := h.cursors
  refine ⟨⟨entries.length, le_rfl, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨by simpa only [prepareCoefficient, DS.rew, List.take_length] using h.supports,
      by simpa only [prepareCoefficient, DS.rew, List.take_length] using h.parities,
      by simpa only [prepareCoefficient, DS.rew, List.take_length] using h.values,
      by simpa (config := {decide := true}) [prepareCoefficient, DS.rew] using hc cacheSupports (by simp),
      by simpa (config := {decide := true}) [prepareCoefficient, DS.rew] using hc cacheParities (by simp),
      by simpa (config := {decide := true}) [prepareCoefficient, DS.rew] using hc cacheValues (by simp)⟩
  · simpa only [prepareCoefficient, DS.rew, List.take_length] using h.outerSupport
  · simpa only [prepareCoefficient, DS.rew, List.take_length] using h.outerParity
  · simpa [prepareCoefficient, DS.rew] using hout
  · simp (config := {decide := true}) [prepareCoefficient, DS.rew]
  · simp (config := {decide := true}) [prepareCoefficient, DS.rew]
  · simpa (config := {decide := true}) [prepareCoefficient, DS.rew] using hcursor

end NearQuarticWires.StageRecovery
