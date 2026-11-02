import Proof.Quartic.StageRecovery.MobScan

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: each coefficient starts
with three genuine sequential rewinds, whose costs are paid in full. -/
def rewindCacheProgram : St VV MM :=
  .seq (.op (.rwM cacheSupports)) (.seq (.op (.rwM cacheParities)) (.op (.rwM cacheValues)))

/-- `lem:print`, paper/paper.tex: the state obtained by
rewinding exactly the three cached support, parity and value streams. -/
def rewindCache (a : DS VV MM) : DS VV MM :=
  ((a.rew cacheSupports).rew cacheParities).rew cacheValues

/-- `lem:print`, paper/paper.tex: rewinding the cache
retains every register and every other source, store or output cursor. -/
theorem cacheRest_rewind (a : DS VV MM) : cacheRest (rewindCache a) = cacheRest a := by
  have h : (fun m : Fin MM => if m ∈ [cacheSupports, cacheParities, cacheValues] then 0
      else (rewindCache a).rc m) =
      (fun m : Fin MM => if m ∈ [cacheSupports, cacheParities, cacheValues] then 0 else a.rc m) := by
    funext m
    fin_cases m <;> simp (config := {decide := true}) [rewindCache, DS.rew, cacheSupports, cacheParities, cacheValues]
  exact congrArg (fun f => (a.ip, a.out, a.ram, f, a.kin, a.kout, a.kc)) h

/-- `lem:print`, paper/paper.tex: the actual rewind
program charges once for every already traversed record of each store. -/
theorem rewindCacheProgram_spec (C : Ctx) (a : DS VV MM) (entries : List CachedValue)
    (k : ℕ) (hcache : CachedAt entries k a) :
    Hs C rewindCacheProgram a (3 * k + 5) (fun b => b = rewindCache a) := by
  unfold rewindCacheProgram
  refine (Hs.seq (t1 := k + 1) (t2 := 2 * k + 3) ((hs_rwM C cacheSupports a).mono
    (by rw [hcache.supportCursor]) (fun _ h => h)) fun b hb => ?_).mono (by omega) (fun _ h => h)
  subst b
  refine (Hs.seq (t1 := k + 1) (t2 := k + 1) ((hs_rwM C cacheParities _).mono
    (by simp (config := {decide := true}) [DS.rew, hcache.parityCursor]) (fun _ h => h))
    fun b hb => ?_).mono (by omega) (fun _ h => h)
  subst b
  exact (hs_rwM C cacheValues _).mono
    (by simp (config := {decide := true}) [DS.rew, hcache.valueCursor]) (fun _ h => h)

/-- `lem:print`, paper/paper.tex: the literal rewind
returns all three cache streams to their true first record. -/
theorem CachedAt.rewind {entries : List CachedValue} {k : ℕ} {a : DS VV MM}
    (h : CachedAt entries k a) : CachedAt entries 0 (rewindCache a) := by
  exact ⟨h.supports, h.parities, h.values,
    by simp (config := {decide := true}) [rewindCache, DS.rew],
    by simp (config := {decide := true}) [rewindCache, DS.rew],
    by simp (config := {decide := true}) [rewindCache, DS.rew]⟩

/-- `lem:print`, paper/paper.tex: an entire coefficient
is formed by zeroing its accumulator, paying the cache rewinds and then
performing one actual linear inclusion–exclusion scan. -/
def coefficientScanProgram : St VV MM :=
  .seq (.op (.zero coefficientVar)) (.seq rewindCacheProgram cachedScanProgram)

/-- `lem:print`, paper/paper.tex: one coefficient is
computed by an actual modular program with a linear cache bound. This
clock includes the three physical rewinds; it assumes no free seek. -/
theorem coefficientScanProgram_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (entries : List CachedValue) (k : ℕ) (hcache : CachedAt entries k a) (hk : k ≤ entries.length)
    (V s parity q : ℕ) (hV : a.env arityVar = V) (hs : a.env supportVar = s)
    (hparity : a.env supportParityVar = parity) (hq : a.env modulusVar = q)
    (hqlt : 0 < q) (hqfit : 2 * q ≤ 2 ^ C.Wd) (hvalues : ∀ e ∈ entries, e.2.2 < q)
    (hVfit : V < 2 ^ C.Wd) (hW : 2 ≤ C.Wd)
    (hcount : a.env cacheCountVar = entries.length) (hcountfit : entries.length < 2 ^ C.Wd) :
    Hs C coefficientScanProgram a (entries.length * (15 * V + 48) + 12) (fun b =>
      b.env coefficientVar = entries.foldl (cachedMobStep q V s parity) 0 ∧
      CachedAt entries entries.length b ∧ cacheRest b = cacheRest a ∧
      Cst b ∧ Fr a b cachedScanScratch) := by
  unfold coefficientScanProgram
  refine (Hs.seq (t2 := (3 * k + 5) + (entries.length * (15 * V + 45) + 4) + 1)
    (hs_zero C coefficientVar a) fun b hb => ?_).mono (by nlinarith) (fun _ h => h)
  subst b
  have hc0 : CachedAt entries k (a.set coefficientVar 0) :=
    ⟨hcache.supports, hcache.parities, hcache.values,
      hcache.supportCursor, hcache.parityCursor, hcache.valueCursor⟩
  refine Hs.seq (rewindCacheProgram_spec C _ entries k hc0) fun b hb => ?_
  subst b
  let start := rewindCache (a.set coefficientVar 0)
  have hstartc : Cst start := Cst.of_fr (T := [coefficientVar]) hc (Fr.set _ _ (by decide)) (by decide)
  refine (cachedScanProgram_spec C start hstartc entries hc0.rewind V s parity q 0
    (by simpa (config := {decide := true}) [start, rewindCache, DS.rew, DS.set] using hV)
    (by simpa (config := {decide := true}) [start, rewindCache, DS.rew, DS.set] using hs)
    (by simpa (config := {decide := true}) [start, rewindCache, DS.rew, DS.set] using hparity)
    (by simpa (config := {decide := true}) [start, rewindCache, DS.rew, DS.set] using hq)
    rfl hqlt hqfit hqlt hvalues hVfit hW
    (by simpa (config := {decide := true}) [start, rewindCache, DS.rew, DS.set] using hcount)
    hcountfit).mono le_rfl ?_
  rintro b ⟨h1, h2, h3, h4, h5⟩
  exact ⟨h1, h2, h3.trans (cacheRest_rewind _), h4,
    Fr.trans (Fr.set _ _ (by decide)) h5⟩

end NearQuarticWires.StageRecovery
