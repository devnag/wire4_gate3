import Proof.Quartic.StageRecovery.MobValue

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: an independent copy
of the original support order is consumed by the outer coefficient loop. -/
def outerSupports : Fin MM := ⟨3, by decide⟩
/-- `lem:print`, paper/paper.tex: an independent outer
degree-parity stream remains untouched by all inner cache rewinds. -/
def outerParities : Fin MM := ⟨4, by decide⟩
/-- `lem:print`, paper/paper.tex: each completed modular
coefficient is appended once in the original support-family order. -/
def coefficientStore : Fin MM := ⟨5, by decide⟩
/-- `lem:print`, paper/paper.tex: the outer support
counter is independent of all inner scan and formula counters. -/
def outerIndexVar : Fin VV := ⟨104, by decide⟩

/-- `lem:print`, paper/paper.tex: the exact coefficient
values in family order, determined by the once-cached evaluations. -/
def cachedCoefficients (q V : ℕ) (entries : List CachedValue) : List ℕ :=
  entries.map fun e => entries.foldl (cachedMobStep q V e.1 e.2.1) 0

/-- `lem:print`, paper/paper.tex: the outer loop
invariant includes actual output records and all advancing store cursors. -/
structure MobOuterAt (q V : ℕ) (entries : List CachedValue) (k : ℕ) (a : DS VV MM) : Prop where
  cached : ∃ j ≤ entries.length, CachedAt entries j a
  supports : a.ram outerSupports = entries.map Prod.fst
  parities : a.ram outerParities = entries.map (fun e => e.2.1)
  coefficients : a.ram coefficientStore = (cachedCoefficients q V entries).take k
  supportCursor : a.rc outerSupports = k
  parityCursor : a.rc outerParities = k
  coefficientCursor : a.rc coefficientStore = k

/-- `lem:print`, paper/paper.tex: an inner scan retains
the contents of every actual record store. -/
theorem cacheRest_ram {a b : DS VV MM} (h : cacheRest b = cacheRest a) : b.ram = a.ram :=
  congrArg (fun x => x.2.2.1) h

/-- `lem:print`, paper/paper.tex: an inner scan retains
every physical record cursor outside its three dedicated cache streams. -/
theorem cacheRest_cursor {a b : DS VV MM} (h : cacheRest b = cacheRest a)
    (m : Fin MM) (hm : m ∉ [cacheSupports, cacheParities, cacheValues]) : b.rc m = a.rc m := by
  have hh := congrArg (fun x => x.2.2.2.1 m) h
  simpa only [cacheRest, hm, if_false] using hh

/-- `lem:print`, paper/paper.tex: a single outer step
reads its next support, pays all rewinds and inner comparisons, and
appends the exact resulting coefficient to a sequential output store. -/
def coefficientOuterProgram : St VV MM :=
  .seq (.op (.rdM outerSupports supportVar))
    (.seq (.op (.rdM outerParities supportParityVar))
      (.seq coefficientScanProgram (.op (.wrM coefficientStore coefficientVar))))

/-- `lem:print`, paper/paper.tex: the work registers of
one outer step exclude its loop counter, original arity and modulus. -/
def coefficientOuterScratch : List (Fin VV) := supportVar :: supportParityVar :: cachedScanScratch

/-- `lem:print`, paper/paper.tex: one actual coefficient
step has one factor of cache length, including paid linear rewinds and
all physical reads and the final output write. -/
theorem coefficientOuterProgram_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (q V : ℕ) (entries : List CachedValue) (k : ℕ) (hk : k < entries.length)
    (ha : MobOuterAt q V entries k a) (hV : a.env arityVar = V)
    (hq : a.env modulusVar = q) (hqlt : 0 < q) (hqfit : 2 * q ≤ 2 ^ C.Wd)
    (hvalues : ∀ e ∈ entries, e.2.2 < q) (hVfit : V < 2 ^ C.Wd) (hW : 2 ≤ C.Wd)
    (hcount : a.env cacheCountVar = entries.length) (hcountfit : entries.length < 2 ^ C.Wd) :
    Hs C coefficientOuterProgram a (entries.length * (15 * V + 48) + 18) (fun b =>
      MobOuterAt q V entries (k + 1) b ∧ Cst b ∧ Fr a b coefficientOuterScratch ∧ b.out = a.out) := by
  obtain ⟨j, hj, hjcache⟩ := ha.cached
  have hget0 : (a.ram outerSupports).getD (a.rc outerSupports) 0 = entries[k].1 := by
    rw [ha.supports, ha.supportCursor, List.getD_eq_getElem _ _ (by simpa using hk)]
    simp
  unfold coefficientOuterProgram
  refine (Hs.seq (t2 := entries.length * (15 * V + 48) + 16)
    (hs_rdM C outerSupports supportVar a (by rw [ha.supports, ha.supportCursor, List.length_map]; exact hk))
    fun b hb => ?_).mono (by omega) (fun _ h => h)
  subst b
  let a1 := (a.set supportVar entries[k].1).adv outerSupports
  have ha1 : (a.set supportVar ((a.ram outerSupports).getD (a.rc outerSupports) 0)).adv outerSupports = a1 := by
    rw [hget0]
  rw [ha1]
  have hget1 : (a1.ram outerParities).getD (a1.rc outerParities) 0 = entries[k].2.1 := by
    simp only [a1, DS.adv, DS.set_ram, DS.set_rc]
    rw [Function.update_of_ne (by decide), ha.parities, ha.parityCursor,
      List.getD_eq_getElem _ _ (by simpa using hk)]
    simp
  refine (Hs.seq (t2 := entries.length * (15 * V + 48) + 14)
    (hs_rdM C outerParities supportParityVar a1 (by
      simpa (config := {decide := true}) [a1, DS.adv, ha.parities, ha.parityCursor] using hk))
    fun b hb => ?_).mono (by omega) (fun _ h => h)
  subst b
  let a2 := (a1.set supportParityVar entries[k].2.1).adv outerParities
  have ha2 : (a1.set supportParityVar ((a1.ram outerParities).getD (a1.rc outerParities) 0)).adv outerParities = a2 := by
    rw [hget1]
  rw [ha2]
  have ha2f : Fr a a2 [supportVar, supportParityVar] := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp [a2, a1, DS.adv, DS.set, Function.update_of_ne hy.1, Function.update_of_ne hy.2]
  have ha2c : Cst a2 := Cst.of_fr hc ha2f (by decide)
  have ha2cache : CachedAt entries j a2 := by
    exact ⟨hjcache.supports, hjcache.parities, hjcache.values,
      by simpa (config := {decide := true}) [a2, a1, DS.adv] using hjcache.supportCursor,
      by simpa (config := {decide := true}) [a2, a1, DS.adv] using hjcache.parityCursor,
      by simpa (config := {decide := true}) [a2, a1, DS.adv] using hjcache.valueCursor⟩
  refine Hs.seq (t2 := 1) (coefficientScanProgram_spec C a2 ha2c entries j ha2cache hj
    V entries[k].1 entries[k].2.1 q
    (by rw [ha2f _ (by decide), hV])
    (by simp (config := {decide := true}) [a2, a1, DS.adv, DS.set])
    (by simp (config := {decide := true}) [a2, a1, DS.adv, DS.set])
    (by rw [ha2f _ (by decide), hq]) hqlt hqfit hvalues hVfit hW
    (by rw [ha2f _ (by decide), hcount]) hcountfit) fun b ⟨hbc, hbcache, hbrest, hbcst, hbf⟩ => ?_
  have hbram : b.ram = a.ram := (cacheRest_ram hbrest).trans rfl
  have hb0 : b.rc outerSupports = k + 1 := by
    rw [cacheRest_cursor hbrest outerSupports (by decide)]
    simp (config := {decide := true}) [a2, a1, DS.adv, ha.supportCursor]
  have hb1 : b.rc outerParities = k + 1 := by
    rw [cacheRest_cursor hbrest outerParities (by decide)]
    simp (config := {decide := true}) [a2, a1, DS.adv, ha.parityCursor]
  have hbo : b.rc coefficientStore = k := by
    rw [cacheRest_cursor hbrest coefficientStore (by decide)]
    simpa (config := {decide := true}) [a2, a1, DS.adv] using ha.coefficientCursor
  have hlen : (b.ram coefficientStore).length = k := by
    rw [hbram, ha.coefficients, List.length_take]
    simp only [cachedCoefficients, List.length_map]
    omega
  refine (hs_wrM C coefficientStore coefficientVar b (by rw [hbo, hlen])).mono le_rfl ?_
  rintro d rfl
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨hbcst.z, hbcst.one, hbcst.two⟩, ?_, ?_⟩
  · exact ⟨entries.length, le_rfl,
      ⟨by simpa (config := {decide := true}) [DS.put] using hbcache.supports,
        by simpa (config := {decide := true}) [DS.put] using hbcache.parities,
        by simpa (config := {decide := true}) [DS.put] using hbcache.values,
        by simpa (config := {decide := true}) [DS.put] using hbcache.supportCursor,
        by simpa (config := {decide := true}) [DS.put] using hbcache.parityCursor,
        by simpa (config := {decide := true}) [DS.put] using hbcache.valueCursor⟩⟩
  · simpa (config := {decide := true}) [DS.put, hbram] using ha.supports
  · simpa (config := {decide := true}) [DS.put, hbram] using ha.parities
  · simp only [DS.put, Function.update_self, hbo, putAt, hlen, lt_self_iff_false, if_false]
    rw [hbram, ha.coefficients, hbc]
    have hcoeff : (cachedCoefficients q V entries)[k]'(by simpa [cachedCoefficients] using hk) =
        entries.foldl (cachedMobStep q V entries[k].1 entries[k].2.1) 0 := by simp [cachedCoefficients]
    rw [← hcoeff, ← List.take_succ_eq_append_getElem]
  · simpa (config := {decide := true}) [DS.put] using hb0
  · simpa (config := {decide := true}) [DS.put] using hb1
  · simp only [DS.put, Function.update_self, hbo]
  · exact Fr.trans (Fr.weaken ha2f (by simp [coefficientOuterScratch]))
      (Fr.weaken hbf (by intro y hy; simp [coefficientOuterScratch, hy]))
  · exact congrArg (fun x => x.2.1) hbrest

end NearQuarticWires.StageRecovery
