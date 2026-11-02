import Proof.Quartic.StageRecovery.CacheWrite

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicGates.Close.Cells NearCubicGates.Close.Expand NearCubicGates.Close.Tabulator
open NearCubicGates.Close.Interfaces.Formats

/-- `lem:print`, paper/paper.tex: the finite cache is
determined by the original generated family and actual modular Formula
evaluations, with no polynomial-value or coefficient input. -/
def pointEntries {V : ℕ} (q : ℕ) (F : Formula V) (points : List (ℕ × ℕ)) : List CachedValue :=
  points.map fun p => (p.1, p.2 % 2, (modAlg q p.1).eval F)

/-- `lem:print`, paper/paper.tex: advancing the original
family record stream does not touch any of the five cache write heads. -/
theorem CachePrefix.advanceFamily {entries : List CachedValue} {k : ℕ} {a : DS VV MM}
    (h : CachePrefix entries k a) : CachePrefix entries k (a.adv familyRecordStore) := by
  refine ⟨h.supports, h.parities, h.values, h.outerSupport, h.outerParity, ?_⟩
  intro m hm
  have hn : m ≠ familyRecordStore := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl <;> decide
  simpa only [DS.adv, Function.update_of_ne hn] using h.cursors m hm

/-- `lem:print`, paper/paper.tex: one original family
record is decoded, evaluated from literal retained Formula bytes, and
written to the finite cache by one actual source program. -/
def buildCachePointProgram : St VV MM :=
  .seq readFamilyPointProgram (.seq cachedEvaluationProgram writeCachedPointProgram)

/-- `lem:print`, paper/paper.tex: a cache-building step
retains the original arity, modulus, family bound and Formula length. -/
def buildCachePointScratch : List (Fin VV) := familyPointScratch ++ cachedEvaluationScratch

/-- `lem:print`, paper/paper.tex: the actual cache
producer evaluates exactly one next family point and restores the input
head before appending its exact reduced result. -/
theorem buildCachePointProgram_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    {V : ℕ} (F : Formula V) (q : ℕ) (points : List (ℕ × ℕ)) (k : ℕ) (hk : k < points.length)
    (hprefix : CachePrefix (pointEntries q F points) k a)
    (hrecords : a.ram familyRecordStore = points.map (packedFamilyRecord V))
    (hcursor : a.rc familyRecordStore = k) (hbase : a.env coordinateBaseVar = 2 ^ V)
    (hpoints : ∀ p ∈ points, p.1 < 2 ^ V) (hq : 2 ≤ q) (haq : a.env modulusVar = q)
    (hcount : a.env tokenCountVar = (toks F).length) (hcountfit : (toks F).length < 2 ^ C.Wd)
    (suffix : List Bool) (hin : C.inp.drop a.ip = tokenStream (toks F) ++ suffix)
    (hwidth : formulaTokenBound F + 5 ≤ C.Wd) (hVwidth : V + 2 ≤ C.Wd)
    (hdepth : q ^ ((toks F).length + 3) ≤ 2 ^ C.Wd)
    (hlength : a.env tokenLengthVar = (tokenStream (toks F)).length)
    (hlengthfit : (tokenStream (toks F)).length < 2 ^ C.Wd) :
    Hs C buildCachePointProgram a (cachedEvaluationCost F + 16) (fun b =>
      CachePrefix (pointEntries q F points) (k + 1) b ∧
      b.ram familyRecordStore = a.ram familyRecordStore ∧ b.rc familyRecordStore = k + 1 ∧
      b.ram coefficientStore = a.ram coefficientStore ∧ b.rc coefficientStore = a.rc coefficientStore ∧
      b.ip = a.ip ∧ Cst b ∧ Fr a b buildCachePointScratch ∧ b.out = a.out) := by
  unfold buildCachePointProgram
  refine (Hs.seq (t2 := cachedEvaluationCost F + 10)
    (readFamilyPointProgram_spec C a hc V points k hk hrecords hcursor hbase
      (hpoints _ (List.getElem_mem hk)) hVwidth) fun b ⟨hbp, hbparity, hbsh, hbc, hbf⟩ => ?_).mono
    (by omega) (fun _ h => h)
  have hbsame := Same.of_sh hbsh
  have hbprefix := hprefix.advanceFamily.of_sh hbsh
  refine Hs.seq (t2 := 9) (cachedEvaluationProgram_spec C b hbc F q points[k].1 suffix hq
    (by rw [hbf _ (by decide), haq]) hbp
    (by rw [hbf _ (by decide), hcount]) hcountfit
    (by rw [hbsame.ip]; exact hin) hwidth hdepth
    (by rw [hbf _ (by decide), hlength]) hlengthfit) fun d ⟨hdv, hdsh, hdc, hdf⟩ => ?_
  have hdsame := Same.of_sh hdsh
  have hdprefix := hbprefix.of_sh hdsh
  have hk' : k < (pointEntries q F points).length := by simpa [pointEntries] using hk
  refine (writeCachedPointProgram_spec C d (hdprefix.room hk'.le)).mono le_rfl ?_
  rintro e rfl
  have hdp : d.env pointVar = points[k].1 := by rw [hdf _ (by decide), hbp]
  have hdparity : d.env candidateParityVar = points[k].2 % 2 := by rw [hdf _ (by decide), hbparity]
  have hwrite := hdprefix.write hk'
    (by simpa [pointEntries] using hdp) (by simpa [pointEntries] using hdparity)
    (by simpa [pointEntries] using hdv)
  refine ⟨hwrite, ?_, ?_, ?_, ?_, ?_, ⟨hdc.z, hdc.one, hdc.two⟩, ?_, ?_⟩
  · simp (config := {decide := true}) [writeCachedPoint, DS.put, hdsame.ram, hbsame.ram, DS.adv]
  · simp (config := {decide := true}) [writeCachedPoint, DS.put, hdsame.rc, hbsame.rc, DS.adv, hcursor]
  · simp (config := {decide := true}) [writeCachedPoint, DS.put, hdsame.ram, hbsame.ram, DS.adv]
  · simp (config := {decide := true}) [writeCachedPoint, DS.put, hdsame.rc, hbsame.rc, DS.adv]
  · exact hdsame.ip.trans hbsame.ip
  · exact Fr.trans (Fr.weaken hbf (by intro y hy; simp [buildCachePointScratch, hy]))
      (Fr.weaken hdf (by intro y hy; simp [buildCachePointScratch, hy]))
  · exact hdsame.out.trans hbsame.out

end NearQuarticWires.StageRecovery
