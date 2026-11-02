import Proof.Quartic.StageRecovery.MobArithmetic

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicGates.Close.Cells NearCubicGates.Close.Expand

/-- `lem:print`, paper/paper.tex: one cached evaluation
stores its characteristic support, degree parity and reduced value. -/
abbrev CachedValue := ℕ × ℕ × ℕ
/-- `lem:print`, paper/paper.tex: a sequential store of
characteristic supports, duplicated once for the inner scan. -/
def cacheSupports : Fin MM := ⟨0, by decide⟩
/-- `lem:print`, paper/paper.tex: the parallel cached
degree-parity stream in its original family order. -/
def cacheParities : Fin MM := ⟨1, by decide⟩
/-- `lem:print`, paper/paper.tex: the parallel stream
of modular values, each evaluated only once before coefficient scanning. -/
def cacheValues : Fin MM := ⟨2, by decide⟩

/-- `lem:print`, paper/paper.tex: the literal three
record stores are aligned at the same sequential family position. -/
structure CachedAt (entries : List CachedValue) (k : ℕ) (a : DS VV MM) : Prop where
  supports : a.ram cacheSupports = entries.map Prod.fst
  parities : a.ram cacheParities = entries.map (fun e => e.2.1)
  values : a.ram cacheValues = entries.map (fun e => e.2.2)
  supportCursor : a.rc cacheSupports = k
  parityCursor : a.rc cacheParities = k
  valueCursor : a.rc cacheValues = k

/-- `lem:print`, paper/paper.tex: consuming one cached
triple advances exactly its three physical record-store cursors. -/
def advanceCache (a : DS VV MM) : DS VV MM :=
  ((a.adv cacheSupports).adv cacheParities).adv cacheValues

/-- `lem:print`, paper/paper.tex: one inclusion–exclusion
summand is determined by original support inclusion and degree parity. -/
def cachedMobStep (q V s parity acc : ℕ) (entry : CachedValue) : ℕ :=
  signedMobStep q (decide (setOf V entry.1 ⊆ setOf V s))
    (decide (parity = entry.2.1)) acc entry.2.2

/-- `lem:print`, paper/paper.tex: one actual inner
pass reads three next records, checks support inclusion and adds the
signed reduced value. No indexed fetch or reevaluation is performed. -/
def cachedMobProgram : St VV MM :=
  .seq (.op (.rdM cacheSupports candidateVar))
    (.seq (.op (.rdM cacheParities candidateParityVar))
      (.seq (.op (.rdM cacheValues sampledValueVar))
        (.seq subsetProgram signedMobProgram)))

/-- `lem:print`, paper/paper.tex: the work registers of
one cache pass exclude the retained outer support, parity and modulus. -/
def cachedMobScratch : List (Fin VV) :=
  [candidateVar, candidateParityVar, sampledValueVar] ++ subsetScratch ++ signedMobScratch

/-- `lem:print`, paper/paper.tex: cached values remain
aligned after exactly one sequential pass, retaining the other stores. -/
theorem CachedAt.advance {entries : List CachedValue} {k : ℕ} {a b : DS VV MM}
    (h : CachedAt entries k a) (hb : b.sh = (advanceCache a).sh) : CachedAt entries (k + 1) b := by
  have he := Same.of_sh hb
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [he.ram]
    exact h.supports
  · rw [he.ram]
    exact h.parities
  · rw [he.ram]
    exact h.values
  · rw [he.rc]
    simpa (config := {decide := true}) [advanceCache, DS.adv] using h.supportCursor
  · rw [he.rc]
    simpa (config := {decide := true}) [advanceCache, DS.adv] using h.parityCursor
  · rw [he.rc]
    simpa (config := {decide := true}) [advanceCache, DS.adv] using h.valueCursor

/-- `lem:print`, paper/paper.tex: the literal inner
pass computes one exact finite modular summand in linear arity time,
preserving the cache contents and all original input/output positions. -/
theorem cachedMobProgram_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (entries : List CachedValue) (k : ℕ) (hk : k < entries.length) (hcache : CachedAt entries k a)
    (V s parity q acc : ℕ) (hV : a.env arityVar = V) (hs : a.env supportVar = s)
    (hparity : a.env supportParityVar = parity) (hq : a.env modulusVar = q)
    (hacc : a.env coefficientVar = acc) (hqlt : 0 < q) (hqfit : 2 * q ≤ 2 ^ C.Wd)
    (hacclt : acc < q) (hvalues : ∀ e ∈ entries, e.2.2 < q)
    (hVfit : V < 2 ^ C.Wd) (hW : 2 ≤ C.Wd) :
    Hs C cachedMobProgram a (15 * V + 41) (fun b =>
      b.env coefficientVar = cachedMobStep q V s parity acc entries[k] ∧
      CachedAt entries (k + 1) b ∧ b.sh = (advanceCache a).sh ∧
      Cst b ∧ Fr a b cachedMobScratch) := by
  have hread0 : a.rc cacheSupports < (a.ram cacheSupports).length := by
    rw [hcache.supportCursor, hcache.supports, List.length_map]
    exact hk
  have hget0 : (a.ram cacheSupports).getD (a.rc cacheSupports) 0 = entries[k].1 := by
    rw [hcache.supports, hcache.supportCursor, List.getD_eq_getElem _ _ (by simpa using hk)]
    simp
  unfold cachedMobProgram
  refine (Hs.seq (t2 := 15 * V + 39) (hs_rdM C cacheSupports candidateVar a hread0)
    fun b hb => ?_).mono (by omega) (fun _ h => h)
  subst b
  let a1 := (a.set candidateVar entries[k].1).adv cacheSupports
  have ha1 : (a.set candidateVar ((a.ram cacheSupports).getD (a.rc cacheSupports) 0)).adv cacheSupports = a1 := by
    rw [hget0]
  rw [ha1]
  have hread1 : a1.rc cacheParities < (a1.ram cacheParities).length := by
    simpa (config := {decide := true}) [a1, DS.adv, hcache.parityCursor, hcache.parities] using hk
  have hget1 : (a1.ram cacheParities).getD (a1.rc cacheParities) 0 = entries[k].2.1 := by
    simp only [a1, DS.adv, DS.set_ram, DS.set_rc]
    rw [Function.update_of_ne (by decide), hcache.parities, hcache.parityCursor,
      List.getD_eq_getElem _ _ (by simpa using hk)]
    simp
  refine (Hs.seq (t2 := 15 * V + 37) (hs_rdM C cacheParities candidateParityVar a1 hread1)
    fun b hb => ?_).mono (by omega) (fun _ h => h)
  subst b
  let a2 := (a1.set candidateParityVar entries[k].2.1).adv cacheParities
  have ha2 : (a1.set candidateParityVar ((a1.ram cacheParities).getD (a1.rc cacheParities) 0)).adv cacheParities = a2 := by
    rw [hget1]
  rw [ha2]
  have hread2 : a2.rc cacheValues < (a2.ram cacheValues).length := by
    simpa (config := {decide := true}) [a2, a1, DS.adv, hcache.valueCursor, hcache.values] using hk
  have hget2 : (a2.ram cacheValues).getD (a2.rc cacheValues) 0 = entries[k].2.2 := by
    simp only [a2, a1, DS.adv, DS.set_ram, DS.set_rc]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      hcache.values, hcache.valueCursor, List.getD_eq_getElem _ _ (by simpa using hk)]
    simp
  refine (Hs.seq (t2 := 15 * V + 35) (hs_rdM C cacheValues sampledValueVar a2 hread2)
    fun b hb => ?_).mono (by omega) (fun _ h => h)
  subst b
  let a3 := (a2.set sampledValueVar entries[k].2.2).adv cacheValues
  have ha3 : (a2.set sampledValueVar ((a2.ram cacheValues).getD (a2.rc cacheValues) 0)).adv cacheValues = a3 := by
    rw [hget2]
  rw [ha3]
  have ha3c : Cst a3 := by
    refine ⟨?_, ?_, ?_⟩ <;> simp (config := {decide := true}) [a3, a2, a1, DS.adv, DS.set, hc.z, hc.one, hc.two]
  have ha3f : Fr a a3 [candidateVar, candidateParityVar, sampledValueVar] := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp [a3, a2, a1, DS.adv, DS.set, Function.update_of_ne hy.1,
      Function.update_of_ne hy.2.1, Function.update_of_ne hy.2.2]
  have ha3sh : a3.sh = (advanceCache a).sh := rfl
  refine (Hs.seq (t2 := 23) (subsetProgram_spec C a3 ha3c V s entries[k].1
    (by rw [ha3f _ (by decide), hV]) (by rw [ha3f _ (by decide), hs])
    (by simp (config := {decide := true}) [a3, a2, a1, DS.adv, DS.set]) hVfit hW)
    fun b ⟨hbs, hbsh, hbc, hbf⟩ => ?_).mono (by omega) (fun _ h => h)
  refine (signedMobProgram_spec C b hbc q acc entries[k].2.2
    (decide (setOf V entries[k].1 ⊆ setOf V s)) (decide (parity = entries[k].2.1)) hqlt hqfit
    (by rw [hbf _ (by decide), ha3f _ (by decide), hq])
    (by rw [hbf _ (by decide), ha3f _ (by decide), hacc])
    (by rw [hbf _ (by decide)]; simp (config := {decide := true}) [a3, a2, a1, DS.adv, DS.set])
    hacclt (hvalues _ (List.getElem_mem hk)) (by simpa using hbs) (by
      rw [hbf _ (by decide), hbf _ (by decide), ha3f _ (by decide), hparity]
      simp (config := {decide := true}) [a3, a2, a1, DS.adv, DS.set])).mono le_rfl ?_
  rintro d ⟨hdc, hdsh, hdcst, hdf⟩
  have hsh : d.sh = (advanceCache a).sh := hdsh.trans (hbsh.trans ha3sh)
  exact ⟨hdc, hcache.advance hsh, hsh, hdcst,
    Fr.trans (Fr.weaken ha3f (by simp [cachedMobScratch]))
      (Fr.trans (Fr.weaken hbf (by intro y hy; simp [cachedMobScratch, hy]))
        (Fr.weaken hdf (by intro y hy; simp [cachedMobScratch, hy])))⟩

end NearQuarticWires.StageRecovery
