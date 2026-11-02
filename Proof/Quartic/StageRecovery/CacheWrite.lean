import Proof.Quartic.StageRecovery.CacheRecord

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: a sequential record
write leaves the entire finite register bank unchanged. -/
@[simp] theorem cachePut_env (a : DS VV MM) (m : Fin MM) (v : ℕ) :
    (a.put m v).env = a.env := rfl

/-- `lem:print`, paper/paper.tex: the selected physical
store is updated at its current sequential write position. -/
@[simp] theorem cachePut_ram_self (a : DS VV MM) (m : Fin MM) (v : ℕ) :
    (a.put m v).ram m = putAt (a.ram m) (a.rc m) v := by simp [DS.put]

/-- `lem:print`, paper/paper.tex: a physical record
write does not modify a different store's contents. -/
@[simp] theorem cachePut_ram_ne (a : DS VV MM) (m n : Fin MM) (v : ℕ) (h : n ≠ m) :
    (a.put m v).ram n = a.ram n := Function.update_of_ne h _ _

/-- `lem:print`, paper/paper.tex: one physical record
write advances exactly its selected store cursor. -/
@[simp] theorem cachePut_rc_self (a : DS VV MM) (m : Fin MM) (v : ℕ) :
    (a.put m v).rc m = a.rc m + 1 := by simp [DS.put]

/-- `lem:print`, paper/paper.tex: every other record
cursor remains fixed by the selected sequential write. -/
@[simp] theorem cachePut_rc_ne (a : DS VV MM) (m n : Fin MM) (v : ℕ) (h : n ≠ m) :
    (a.put m v).rc n = a.rc n := Function.update_of_ne h _ _

/-- `lem:print`, paper/paper.tex: a cached point is
written once to the inner streams and to the two independent outer
metadata streams; its Formula value is not duplicated or reevaluated. -/
def writeCachedPointProgram : St VV MM :=
  .seq (.op (.wrM cacheSupports pointVar))
    (.seq (.op (.wrM cacheParities candidateParityVar))
      (.seq (.op (.wrM cacheValues stackVar))
        (.seq (.op (.wrM outerSupports pointVar)) (.op (.wrM outerParities candidateParityVar)))))

/-- `lem:print`, paper/paper.tex: the exact five
sequential writes retain all registers, input bytes and other stores. -/
def writeCachedPoint (a : DS VV MM) : DS VV MM :=
  ((((a.put cacheSupports (a.env pointVar)).put cacheParities (a.env candidateParityVar)).put
    cacheValues (a.env stackVar)).put outerSupports (a.env pointVar)).put outerParities (a.env candidateParityVar)

/-- `lem:print`, paper/paper.tex: the genuine cache
write is a fixed nine-operation source program, including sequencing. -/
theorem writeCachedPointProgram_spec (C : Ctx) (a : DS VV MM)
    (hroom : ∀ m ∈ [cacheSupports, cacheParities, cacheValues, outerSupports, outerParities],
      a.rc m ≤ (a.ram m).length) :
    Hs C writeCachedPointProgram a 9 (fun b => b = writeCachedPoint a) := by
  unfold writeCachedPointProgram
  refine Hs.seq (t2 := 7) (hs_wrM C cacheSupports pointVar a (hroom _ (by simp))) fun b hb => ?_
  subst b
  refine Hs.seq (t2 := 5) (hs_wrM C cacheParities candidateParityVar _
    (by simpa (config := {decide := true}) [DS.put] using hroom cacheParities (by simp))) fun b hb => ?_
  subst b
  refine Hs.seq (t2 := 3) (hs_wrM C cacheValues stackVar _
    (by simpa (config := {decide := true}) [DS.put] using hroom cacheValues (by simp))) fun b hb => ?_
  subst b
  refine Hs.seq (t2 := 1) (hs_wrM C outerSupports pointVar _
    (by simpa (config := {decide := true}) [DS.put] using hroom outerSupports (by simp))) fun b hb => ?_
  subst b
  exact hs_wrM C outerParities candidateParityVar _
    (by simpa (config := {decide := true}) [DS.put] using hroom outerParities (by simp))

/-- `lem:print`, paper/paper.tex: a cache prefix
contains only the already processed original support evaluations. -/
structure CachePrefix (entries : List CachedValue) (k : ℕ) (a : DS VV MM) : Prop where
  supports : a.ram cacheSupports = (entries.take k).map Prod.fst
  parities : a.ram cacheParities = (entries.take k).map (fun e => e.2.1)
  values : a.ram cacheValues = (entries.take k).map (fun e => e.2.2)
  outerSupport : a.ram outerSupports = (entries.take k).map Prod.fst
  outerParity : a.ram outerParities = (entries.take k).map (fun e => e.2.1)
  cursors : ∀ m ∈ [cacheSupports, cacheParities, cacheValues, outerSupports, outerParities], a.rc m = k

/-- `lem:print`, paper/paper.tex: a cache prefix leaves
exactly enough sequential room for its next original family record. -/
theorem CachePrefix.room {entries : List CachedValue} {k : ℕ} {a : DS VV MM}
    (h : CachePrefix entries k a) (hk : k ≤ entries.length) :
    ∀ m ∈ [cacheSupports, cacheParities, cacheValues, outerSupports, outerParities],
      a.rc m ≤ (a.ram m).length := by
  intro m hm
  rw [h.cursors m hm]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl <;>
    simp only [h.supports, h.parities, h.values, h.outerSupport, h.outerParity,
      List.length_map, List.length_take, min_eq_left hk] <;> exact le_rfl

/-- `lem:print`, paper/paper.tex: actual input-head or
arithmetic operations retaining the non-register state retain the exact
cache prefix and all five physical write cursors. -/
theorem CachePrefix.of_sh {entries : List CachedValue} {k : ℕ} {a b : DS VV MM}
    (h : CachePrefix entries k a) (hb : b.sh = a.sh) : CachePrefix entries k b := by
  have he := Same.of_sh hb
  exact ⟨by rw [he.ram]; exact h.supports, by rw [he.ram]; exact h.parities,
    by rw [he.ram]; exact h.values, by rw [he.ram]; exact h.outerSupport,
    by rw [he.ram]; exact h.outerParity, fun m hm => by rw [he.rc]; exact h.cursors m hm⟩

/-- `lem:print`, paper/paper.tex: five actual appends
extend the cached prefix by exactly the next original computed point. -/
theorem CachePrefix.write {entries : List CachedValue} {k : ℕ} {a : DS VV MM}
    (h : CachePrefix entries k a) (hk : k < entries.length)
    (hp : a.env pointVar = entries[k].1) (hd : a.env candidateParityVar = entries[k].2.1)
    (hv : a.env stackVar = entries[k].2.2) : CachePrefix entries (k + 1) (writeCachedPoint a) := by
  have hlen : (entries.take k).length = k := by simp only [List.length_take, min_eq_left hk.le]
  have htake := List.take_succ_eq_append_getElem hk
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp (config := {decide := true}) only [writeCachedPoint, cachePut_env, cachePut_ram_self, cachePut_ram_ne, cachePut_rc_self, cachePut_rc_ne]
    rw [h.supports, h.cursors cacheSupports (by simp), hp]
    simp only [putAt, List.length_map, hlen, lt_self_iff_false, if_false]
    rw [htake, List.map_append, List.map_singleton]
  · simp (config := {decide := true}) only [writeCachedPoint, cachePut_env, cachePut_ram_self, cachePut_ram_ne, cachePut_rc_self, cachePut_rc_ne]
    rw [h.parities, h.cursors cacheParities (by simp), hd]
    simp only [putAt, List.length_map, hlen, lt_self_iff_false, if_false]
    rw [htake, List.map_append, List.map_singleton]
  · simp (config := {decide := true}) only [writeCachedPoint, cachePut_env, cachePut_ram_self, cachePut_ram_ne, cachePut_rc_self, cachePut_rc_ne]
    rw [h.values, h.cursors cacheValues (by simp), hv]
    simp only [putAt, List.length_map, hlen, lt_self_iff_false, if_false]
    rw [htake, List.map_append, List.map_singleton]
  · simp (config := {decide := true}) only [writeCachedPoint, cachePut_env, cachePut_ram_self, cachePut_ram_ne, cachePut_rc_self, cachePut_rc_ne]
    rw [h.outerSupport, h.cursors outerSupports (by simp), hp]
    simp only [putAt, List.length_map, hlen, lt_self_iff_false, if_false]
    rw [htake, List.map_append, List.map_singleton]
  · simp (config := {decide := true}) only [writeCachedPoint, cachePut_env, cachePut_ram_self, cachePut_ram_ne, cachePut_rc_self, cachePut_rc_ne]
    rw [h.outerParity, h.cursors outerParities (by simp), hd]
    simp only [putAt, List.length_map, hlen, lt_self_iff_false, if_false]
    rw [htake, List.map_append, List.map_singleton]
  · intro m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl <;>
      simp (config := {decide := true}) only [writeCachedPoint, cachePut_rc_self, cachePut_rc_ne,
        h.cursors cacheSupports (by simp), h.cursors cacheParities (by simp),
        h.cursors cacheValues (by simp), h.cursors outerSupports (by simp), h.cursors outerParities (by simp)]

end NearQuarticWires.StageRecovery
