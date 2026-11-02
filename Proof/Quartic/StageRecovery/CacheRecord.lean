import Proof.Quartic.StageRecovery.CacheEval
import Proof.Quartic.StageRecovery.MobDriver

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicGates.Close.Cells NearCubicGates.Close.Expand NearCubicGates.Close.Tabulator

/-- `lem:print`, paper/paper.tex: the original generated
support records are consumed once while their modular values are cached. -/
def familyRecordStore : Fin MM := ⟨6, by decide⟩
/-- `lem:print`, paper/paper.tex: one packed original
family record contains the support and its actual degree. -/
def familyRecordVar : Fin VV := ⟨108, by decide⟩
/-- `lem:print`, paper/paper.tex: the characteristic
support radix is exactly two to the original Formula arity. -/
def coordinateBaseVar : Fin VV := ⟨109, by decide⟩
/-- `lem:print`, paper/paper.tex: division of a generated
family record recovers its original degree before computing parity. -/
def familyDegreeVar : Fin VV := ⟨110, by decide⟩
/-- `lem:print`, paper/paper.tex: the quotient work
register used only when computing the family degree parity. -/
def familyHalfDegreeVar : Fin VV := ⟨111, by decide⟩

/-- `lem:print`, paper/paper.tex: the literal generated
family representation has separate support and degree fields. -/
def packedFamilyRecord (V : ℕ) (p : ℕ × ℕ) : ℕ := p.1 + p.2 * 2 ^ V

/-- `lem:print`, paper/paper.tex: the actual next-record
read is followed by two binary divisions to recover support and parity. -/
def readFamilyPointProgram : St VV MM :=
  .seq (.op (.rdM familyRecordStore familyRecordVar))
    (.seq (.op (.dm familyRecordVar coordinateBaseVar familyDegreeVar pointVar))
      (.op (.dm familyDegreeVar v2 familyHalfDegreeVar candidateParityVar)))

/-- `lem:print`, paper/paper.tex: decoding a generated
family point modifies only its declared finite work registers. -/
def familyPointScratch : List (Fin VV) :=
  [familyRecordVar, familyDegreeVar, pointVar, familyHalfDegreeVar, candidateParityVar]

/-- `lem:print`, paper/paper.tex: the next literal
family record is consumed exactly once and decoded to its genuine
characteristic point and original degree parity. -/
theorem readFamilyPointProgram_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (V : ℕ) (points : List (ℕ × ℕ)) (k : ℕ) (hk : k < points.length)
    (hrecords : a.ram familyRecordStore = points.map (packedFamilyRecord V))
    (hcursor : a.rc familyRecordStore = k) (hbase : a.env coordinateBaseVar = 2 ^ V)
    (hfit : points[k].1 < 2 ^ V) (hwidth : V + 2 ≤ C.Wd) :
    Hs C readFamilyPointProgram a 5 (fun b =>
      b.env pointVar = points[k].1 ∧ b.env candidateParityVar = points[k].2 % 2 ∧
      b.sh = (a.adv familyRecordStore).sh ∧ Cst b ∧ Fr a b familyPointScratch) := by
  have hread : a.rc familyRecordStore < (a.ram familyRecordStore).length := by
    rw [hcursor, hrecords, List.length_map]
    exact hk
  have hget : (a.ram familyRecordStore).getD (a.rc familyRecordStore) 0 = packedFamilyRecord V points[k] := by
    rw [hcursor, hrecords, List.getD_eq_getElem _ _ (by simpa using hk)]
    simp
  have h2base : 2 * 2 ^ V ≤ 2 ^ C.Wd := by
    rw [show 2 * 2 ^ V = 2 ^ (V + 1) by ring]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hfour : 4 ≤ 2 ^ C.Wd := by
    exact (show 4 = 2 ^ 2 by norm_num).le.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hlow : packedFamilyRecord V points[k] % 2 ^ V = points[k].1 := by
    rw [packedFamilyRecord, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hfit]
  have hhigh : packedFamilyRecord V points[k] / 2 ^ V = points[k].2 := by
    rw [packedFamilyRecord, mul_comm points[k].2, Nat.add_mul_div_left _ _ (Nat.two_pow_pos V),
      Nat.div_eq_of_lt hfit, zero_add]
  unfold readFamilyPointProgram
  refine Hs.seq (t2 := 3) (hs_rdM C familyRecordStore familyRecordVar a hread) fun b hb => ?_
  subst b
  let start := (a.set familyRecordVar (packedFamilyRecord V points[k])).adv familyRecordStore
  have hstart : (a.set familyRecordVar ((a.ram familyRecordStore).getD (a.rc familyRecordStore) 0)).adv familyRecordStore = start := by
    rw [hget]
  rw [hstart]
  refine Hs.seq (t2 := 1) (hs_dm C familyRecordVar coordinateBaseVar familyDegreeVar pointVar start
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simp (config := {decide := true}) [start, DS.adv, DS.set, hbase])
    (by simpa (config := {decide := true}) [start, DS.adv, DS.set, hbase] using h2base)) fun b hb => ?_
  subst b
  refine (hs_dm C familyDegreeVar v2 familyHalfDegreeVar candidateParityVar _
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simp (config := {decide := true}) [start, DS.adv, DS.set, hc.two])
    (by simpa (config := {decide := true}) [start, DS.adv, DS.set, hc.two] using hfour)).mono le_rfl ?_
  rintro b rfl
  refine ⟨?_, ?_, rfl, ?_, ?_⟩
  · simp (config := {decide := true}) [start, DS.adv, DS.set, hbase, hlow]
  · simp (config := {decide := true}) [start, DS.adv, DS.set, hbase, hc.two, hhigh]
  · refine ⟨?_, ?_, ?_⟩ <;> simp (config := {decide := true}) [start, DS.adv, DS.set, hc.z, hc.one, hc.two]
  · intro y hy
    simp only [familyPointScratch, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp [start, DS.adv, DS.set, Function.update_of_ne hy.1, Function.update_of_ne hy.2.1,
      Function.update_of_ne hy.2.2.1, Function.update_of_ne hy.2.2.2.1, Function.update_of_ne hy.2.2.2.2]

end NearQuarticWires.StageRecovery
