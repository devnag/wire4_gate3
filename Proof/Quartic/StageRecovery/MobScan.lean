import Proof.Quartic.StageRecovery.MobCache

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: the inner scan counter
is separate from the characteristic-bit and postfix-token counters. -/
def cacheIndexVar : Fin VV := ⟨99, by decide⟩
/-- `lem:print`, paper/paper.tex: the once-computed
complete support-family length bounds each sequential cache scan. -/
def cacheCountVar : Fin VV := ⟨103, by decide⟩

/-- `lem:print`, paper/paper.tex: the part of a state
outside the three advancing cache cursors is retained by every scan. -/
def cacheRest (a : DS VV MM) :=
  (a.ip, a.out, a.ram,
    fun m : Fin MM => if m ∈ [cacheSupports, cacheParities, cacheValues] then 0 else a.rc m,
    a.kin, a.kout, a.kc)

/-- `lem:print`, paper/paper.tex: changing a work
register does not alter any actual source, output or record store. -/
@[simp] theorem cacheRest_set (a : DS VV MM) (x : Fin VV) (value : ℕ) :
    cacheRest (a.set x value) = cacheRest a := rfl

/-- `lem:print`, paper/paper.tex: one sequential cache
advance retains all other physical cursors and contents. -/
theorem cacheRest_advance (a : DS VV MM) : cacheRest (advanceCache a) = cacheRest a := by
  have h : (fun m : Fin MM => if m ∈ [cacheSupports, cacheParities, cacheValues] then 0
      else (advanceCache a).rc m) =
      (fun m : Fin MM => if m ∈ [cacheSupports, cacheParities, cacheValues] then 0 else a.rc m) := by
    funext m
    fin_cases m <;> simp (config := {decide := true}) [advanceCache, DS.adv, cacheSupports, cacheParities, cacheValues]
  exact congrArg (fun f => (a.ip, a.out, a.ram, f, a.kin, a.kout, a.kc)) h

/-- `lem:print`, paper/paper.tex: equal complete
non-register state gives equal retained cache-exterior state. -/
theorem cacheRest_of_sh {a b : DS VV MM} (h : b.sh = a.sh) : cacheRest b = cacheRest a := by
  have he := Same.of_sh h
  simp only [cacheRest, he.ip, he.out, he.ram, he.rc, he.kin, he.kout, he.kc]

/-- `lem:print`, paper/paper.tex: each finite modular
update remains inside the declared recovery-residue interval. -/
theorem cachedMobStep_lt (q V s parity acc : ℕ) (e : CachedValue) (hq : 0 < q) (ha : acc < q) :
    cachedMobStep q V s parity acc e < q := by
  unfold cachedMobStep signedMobStep
  split_ifs <;> first | exact Nat.mod_lt _ hq | exact ha

/-- `lem:print`, paper/paper.tex: every prefix of the
sequential modular coefficient sum fits the original finite modulus. -/
theorem cachedMobFold_lt (q V s parity acc : ℕ) (entries : List CachedValue)
    (hq : 0 < q) (ha : acc < q) :
    entries.foldl (cachedMobStep q V s parity) acc < q := by
  induction entries generalizing acc with
  | nil => exact ha
  | cons e entries ih => exact ih _ (cachedMobStep_lt q V s parity acc e hq ha)

/-- `lem:print`, paper/paper.tex: one complete actual
inner scan adds each cached signed point value exactly once. -/
def cachedScanProgram : St VV MM := forS cacheIndexVar cacheCountVar cachedMobProgram

/-- `lem:print`, paper/paper.tex: the finite register
frame of an entire cache scan excludes outer support metadata. -/
def cachedScanScratch : List (Fin VV) := cacheIndexVar :: cachedMobScratch

/-- `lem:print`, paper/paper.tex: the complete actual
scan performs one linear pass through the aligned cache. Its source
clock has one factor of family length, with all other stores retained. -/
theorem cachedScanProgram_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (entries : List CachedValue) (hcache : CachedAt entries 0 a)
    (V s parity q acc : ℕ) (hV : a.env arityVar = V) (hs : a.env supportVar = s)
    (hparity : a.env supportParityVar = parity) (hq : a.env modulusVar = q)
    (hacc : a.env coefficientVar = acc) (hqlt : 0 < q) (hqfit : 2 * q ≤ 2 ^ C.Wd)
    (hacclt : acc < q) (hvalues : ∀ e ∈ entries, e.2.2 < q)
    (hVfit : V < 2 ^ C.Wd) (hW : 2 ≤ C.Wd)
    (hcount : a.env cacheCountVar = entries.length) (hcountfit : entries.length < 2 ^ C.Wd) :
    Hs C cachedScanProgram a (entries.length * (15 * V + 45) + 4) (fun b =>
      b.env coefficientVar = entries.foldl (cachedMobStep q V s parity) acc ∧
      CachedAt entries entries.length b ∧ cacheRest b = cacheRest a ∧
      Cst b ∧ Fr a b cachedScanScratch) := by
  let I : ℕ → DS VV MM → Prop := fun k b =>
    b.env coefficientVar = (entries.take k).foldl (cachedMobStep q V s parity) acc ∧
    CachedAt entries k b ∧ cacheRest b = cacheRest a ∧ Cst b ∧ Fr a b cachedScanScratch
  unfold cachedScanProgram
  refine (forS_spec' (C := C) cacheIndexVar cacheCountVar (by decide) cachedMobProgram
    a entries.length hcountfit I (15 * V + 41) ?_ ?_ hcount ?_).mono (by simp) ?_
  · intro k b value ⟨h1, h2, h3, h4, h5⟩
    exact ⟨by simpa (config := {decide := true}) [DS.set] using h1,
      ⟨h2.supports, h2.parities, h2.values, h2.supportCursor, h2.parityCursor, h2.valueCursor⟩, by simpa using h3, Cst.of_fr h4 (Fr.set _ _ (by decide : cacheIndexVar ∈ [cacheIndexVar])) (by decide),
      Fr.trans h5 (Fr.set _ _ (by simp [cachedScanScratch]))⟩
  · exact ⟨by simpa using hacc, hcache, rfl, hc, Fr.refl _ _⟩
  · intro k hk b ⟨h1, h2, h3, h4, h5⟩ hbi hbn
    have hbV : b.env arityVar = V := by rw [h5 _ (by decide), hV]
    have hbs : b.env supportVar = s := by rw [h5 _ (by decide), hs]
    have hbp : b.env supportParityVar = parity := by rw [h5 _ (by decide), hparity]
    have hbq : b.env modulusVar = q := by rw [h5 _ (by decide), hq]
    refine (cachedMobProgram_spec C b h4 entries k hk h2 V s parity q
      ((entries.take k).foldl (cachedMobStep q V s parity) acc) hbV hbs hbp hbq h1 hqlt hqfit
      (cachedMobFold_lt _ _ _ _ _ _ hqlt hacclt) hvalues hVfit hW).mono le_rfl ?_
    rintro d ⟨hd1, hd2, hd3, hd4, hd5⟩
    have hrest : cacheRest d = cacheRest b := (cacheRest_of_sh hd3).trans (cacheRest_advance b)
    refine ⟨⟨?_, hd2, hrest.trans h3, hd4,
      Fr.trans h5 (Fr.weaken hd5 (by intro y hy; simp [cachedScanScratch, hy]))⟩,
      by rw [hd5 _ (by decide), hbi], by rw [hd5 _ (by decide), hbn]⟩
    rw [List.take_succ_eq_append_getElem hk, List.foldl_append]
    exact hd1
  · rintro b ⟨⟨h1, h2, h3, h4, h5⟩, _, _⟩
    exact ⟨by simpa only [List.take_length] using h1, h2, h3, h4, h5⟩

end NearQuarticWires.StageRecovery
