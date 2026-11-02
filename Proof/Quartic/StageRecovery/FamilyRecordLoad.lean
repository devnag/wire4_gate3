import Proof.Quartic.StageRecovery.CacheWrite
import Proof.Quartic.StageRecovery.FamilyHeader

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: each actual native
family record is read from its finite frame and appended once to the
original generated-record store. -/
def loadFamilyRecordProgram : St VV MM :=
  .seq rdRec (.op (.wrM familyRecordStore t3))

/-- `lem:print`, paper/paper.tex: the physical family
record loader uses only the existing binary reader's work registers. -/
def familyLoadScratch : List (Fin VV) := [t0, t1, t3, vJ]

/-- `lem:print`, paper/paper.tex: one native record is
read from its actual frame and appended in its original order, retaining
every other store, all output and callee buffers, and the exact input cursor. -/
theorem loadFamilyRecordProgram_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (W value : ℕ) (rest : List Bool) (previousRecords : List ℕ)
    (hin : C.inp.drop a.ip = frame (binary W value) ++ rest)
    (hvalue : value < 2 ^ W) (hW : W + 2 ≤ C.Wd)
    (hstore : a.ram familyRecordStore = previousRecords) (hcursor : a.rc familyRecordStore = previousRecords.length) :
    Hs C loadFamilyRecordProgram a (12 * W + 14) (fun b =>
      b.ip = a.ip + (2 * W + 1) ∧ b.out = a.out ∧
      b.ram = Function.update a.ram familyRecordStore (previousRecords ++ [value]) ∧
      b.rc = Function.update a.rc familyRecordStore (previousRecords.length + 1) ∧
      b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧ Cst b ∧ Fr a b familyLoadScratch) := by
  unfold loadFamilyRecordProgram
  refine (Hs.seq (t2 := 1) (rdRec_spec a hc W value rest hin hvalue hW)
    fun b ⟨hbv, hbi, hbr, hbf⟩ => ?_).mono (by omega) (fun _ h => h)
  simp only [Prod.mk.injEq] at hbr
  obtain ⟨hbo, hbram, hbrc, hbkin, hbkout, hbkc⟩ := hbr
  have hbc : Cst b := Cst.of_fr hc hbf (by decide)
  refine (hs_wrM C familyRecordStore t3 b (by rw [hbram, hbrc, hcursor, hstore])).mono le_rfl ?_
  rintro d rfl
  refine ⟨hbi, hbo, ?_, ?_, hbkin, hbkout, hbkc, ⟨hbc.z, hbc.one, hbc.two⟩, hbf⟩
  · simp only [DS.put, hbv, hbram, hbrc, hcursor, hstore, putAt, lt_self_iff_false, if_false]
  · simp only [DS.put, hbrc, hcursor]

end NearQuarticWires.StageRecovery
