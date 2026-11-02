import Proof.Quartic.StageRecovery.CachedCoefficientValues
import Proof.Quartic.StageRecovery.MonomialCodec

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicGates.Close.Cells NearCubicGates.Close.Expand
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats

/-- `lem:print`, paper/paper.tex: the two physical
record streams pair each original support with its actually computed
canonical modular coefficient. -/
def cachedTermRecords (q V : ℕ) (entries : List CachedValue) : List (ℕ × ℕ) :=
  entries.map fun e => (e.1, entries.foldl (cachedMobStep q V e.1 e.2.1) 0)

/-- `lem:print`, paper/paper.tex: the logical Terms
correspond exactly to the two aligned physical record streams. -/
def termsOfRecords (V : ℕ) (records : List (ℕ × ℕ)) : Terms V :=
  records.map fun p => (setOf V p.1, (p.2 : ℤ))

/-- `lem:print`, paper/paper.tex: the actual
coefficient-record stream has precisely the canonical bounded Terms
values and order, including every zero coefficient. -/
theorem termsOfRecords_cached {V : ℕ} (q : ℕ) (hq : 0 < q) (F : Formula V) (D : ℕ) :
    termsOfRecords V (cachedTermRecords q V (boundedFormulaCache q F D)) =
      boundedModTerms q F D := by
  unfold termsOfRecords cachedTermRecords boundedFormulaCache pointEntries boundedModTerms
  rw [List.map_map, List.map_map, ← famPairs_supports, List.map_map]
  apply List.map_congr_left
  intro p hp
  have h := boundedFormulaCache_value q hq F D p hp
  change (setOf V p.1, (((boundedFormulaCache q F D).foldl
    (cachedMobStep q V p.1 (p.2 % 2)) 0 : ℕ) : ℤ)) =
      (setOf V p.1, coeff F.expand (setOf V p.1) % (q : ℤ))
  rw [h, Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))]

/-- `lem:print`, paper/paper.tex: two physical
sequential read heads point to the same original term position. -/
structure TermStreamAt (records : List (ℕ × ℕ)) (k : ℕ) (a : DS VV MM) : Prop where
  supports : a.ram outerSupports = records.map Prod.fst
  coefficients : a.ram coefficientStore = records.map Prod.snd
  supportCursor : a.rc outerSupports = k
  coefficientCursor : a.rc coefficientStore = k

/-- `lem:print`, paper/paper.tex: a register update
retains both actual aligned source stores and their physical positions. -/
theorem TermStreamAt.set {records : List (ℕ × ℕ)} {k : ℕ} {a : DS VV MM}
    (h : TermStreamAt records k a) (x : Fin VV) (value : ℕ) :
    TermStreamAt records k (a.set x value) :=
  ⟨h.supports, h.coefficients, h.supportCursor, h.coefficientCursor⟩

/-- `lem:print`, paper/paper.tex: one term consumes
the next support and actual coefficient before writing its canonical word. -/
def emitTermStep : St VV MM :=
  .seq (.op (.rdM outerSupports supportVar))
    (.seq (.op (.rdM coefficientStore coefficientVar)) emitMonomialProgram)

/-- `lem:print`, paper/paper.tex: a term's actual
two reads and canonical serialization retain the finite request metadata. -/
def emitTermScratch : List (Fin VV) := supportVar :: coefficientVar :: monomialScratch

/-- `lem:print`, paper/paper.tex: the physical term
step consumes precisely the next aligned pair and emits its complete
canonical monomial bytes, with the actual head increments included. -/
theorem emitTermStep_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (V q : ℕ) (records : List (ℕ × ℕ)) (k : ℕ) (hk : k < records.length)
    (ha : TermStreamAt records k a) (hV : a.env arityVar = V)
    (hvalues : ∀ p ∈ records, p.2 < q) (hW : 2 ≤ C.Wd)
    (hVfit : V + 3 < 2 ^ C.Wd) (hzero : natBitLength 0 + 2 < 2 ^ C.Wd)
    (hqfit : natBitLength q + 2 < 2 ^ C.Wd) :
    Hs C emitTermStep a (monomialCost V q + 4) (fun b =>
      TermStreamAt records (k + 1) b ∧
      b.out = a.out ++ monoWord (setOf V records[k].1, (records[k].2 : ℤ)) ∧
      Cst b ∧ Fr a b emitTermScratch) := by
  have hgetS : (a.ram outerSupports).getD (a.rc outerSupports) 0 = records[k].1 := by
    rw [ha.supports, ha.supportCursor, List.getD_eq_getElem _ _ (by simpa using hk)]
    simp
  unfold emitTermStep
  refine (Hs.seq (t2 := monomialCost V q + 2)
    (hs_rdM C outerSupports supportVar a
      (by rw [ha.supports, ha.supportCursor, List.length_map]; exact hk)) fun b hb => ?_).mono
      (by omega) (fun _ h => h)
  subst b
  let a1 := (a.set supportVar records[k].1).adv outerSupports
  have ha1 : (a.set supportVar ((a.ram outerSupports).getD (a.rc outerSupports) 0)).adv outerSupports = a1 := by
    rw [hgetS]
  rw [ha1]
  have hgetC : (a1.ram coefficientStore).getD (a1.rc coefficientStore) 0 = records[k].2 := by
    simp only [a1, DS.adv, DS.set_ram, DS.set_rc]
    rw [Function.update_of_ne (by decide), ha.coefficients, ha.coefficientCursor,
      List.getD_eq_getElem _ _ (by simpa using hk)]
    simp
  refine (Hs.seq (t2 := monomialCost V q)
    (hs_rdM C coefficientStore coefficientVar a1 (by
      simpa (config := {decide := true}) [a1, DS.adv, ha.coefficients, ha.coefficientCursor] using hk))
    fun b hb => ?_).mono (by omega) (fun _ h => h)
  subst b
  let a2 := (a1.set coefficientVar records[k].2).adv coefficientStore
  have ha2 : (a1.set coefficientVar ((a1.ram coefficientStore).getD (a1.rc coefficientStore) 0)).adv coefficientStore = a2 := by
    rw [hgetC]
  rw [ha2]
  have ha2f : Fr a a2 [supportVar, coefficientVar] := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp [a2, a1, DS.adv, DS.set, Function.update_of_ne hx.1, Function.update_of_ne hx.2]
  have ha2c : Cst a2 := Cst.of_fr hc ha2f (by decide)
  have hcbit : natBitLength records[k].2 ≤ natBitLength q := by
    apply NearCubicGates.Close.WorkerArith.WorkerBounds.nbl_le_of_lt (by unfold natBitLength; omega)
    exact (hvalues _ (List.getElem_mem hk)).trans (lt_natBitLength _)
  refine (emitMonomialProgram_spec C a2 ha2c V records[k].1 records[k].2
    (by rw [ha2f _ (by decide), hV])
    (by simp (config := {decide := true}) [a2, a1, DS.adv, DS.set])
    (by simp (config := {decide := true}) [a2, a1, DS.adv, DS.set])
    hW hVfit hzero (by omega)).mono (by unfold monomialCost; omega) ?_
  rintro b ⟨hbo, hbr, hbc, hbf⟩
  have hbram : b.ram = a.ram := congrArg (fun x => x.2.1) hbr
  have hbrc : b.rc = a2.rc := congrArg (fun x => x.2.2.1) hbr
  refine ⟨⟨(congrFun hbram outerSupports).trans ha.supports,
    (congrFun hbram coefficientStore).trans ha.coefficients, ?_, ?_⟩,
    hbo, hbc, Fr.trans (Fr.weaken ha2f (by decide)) (Fr.weaken hbf (by decide))⟩
  · rw [hbrc]
    simp (config := {decide := true}) [a2, a1, DS.adv, ha.supportCursor]
  · rw [hbrc]
    simp (config := {decide := true}) [a2, a1, DS.adv, ha.coefficientCursor]

end NearQuarticWires.StageRecovery
