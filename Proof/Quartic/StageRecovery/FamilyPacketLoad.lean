import Proof.Quartic.StageRecovery.FamilyPacketStep

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: an actual native
packet is parsed until its real delimiter, while its record count is
computed by one charged increment per parsed record. -/
def loadFamilyPacketProgram : St VV MM :=
  .seq (.op (.zero cacheCountVar))
    (.seq readFamilyMarkerProgram (.loop (.eq t0 v1) familyPacketStepProgram))

/-- `lem:print`, paper/paper.tex: marker-driven physical
parsing loads the entire generated family and derives its exact count.
No callee-output-length observation or supplied count is used. -/
theorem loadFamilyPacketProgram_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (W : ℕ) (records : List ℕ) (suffix : List Bool) (hWpos : 0 < W) (hW : W + 2 ≤ C.Wd)
    (hfit : ∀ x ∈ records, x < 2 ^ W) (hcountfit : records.length < 2 ^ C.Wd)
    (hin : C.inp.drop a.ip = nativeFamilyPacket W records ++ suffix)
    (hstore : a.ram familyRecordStore = []) (hcursor : a.rc familyRecordStore = 0) :
    Hs C loadFamilyPacketProgram a (records.length * (12 * W + 22) + 6) (fun b =>
      b.env cacheCountVar = records.length ∧ b.env t0 = 0 ∧
      b.ip = a.ip + (nativeFamilyPacket W records).length ∧ b.out = a.out ∧
      b.ram = Function.update a.ram familyRecordStore records ∧
      b.rc = Function.update a.rc familyRecordStore records.length ∧
      b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧ Cst b ∧ Fr a b familyPacketScratch) := by
  let I : ℕ → DS VV MM → Prop := fun k b =>
    b.env cacheCountVar = k ∧ b.env t0 = (if k < records.length then 1 else 0) ∧
    b.ip = a.ip + k * (2 * W + 1) + 1 ∧ b.out = a.out ∧
    b.ram = Function.update a.ram familyRecordStore (records.take k) ∧
    b.rc = Function.update a.rc familyRecordStore k ∧
    b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧ Cst b ∧ Fr a b familyPacketScratch
  have hloop : ∀ b, I 0 b → Hs C (.loop (.eq t0 v1) familyPacketStepProgram) b
      (records.length * (12 * W + 22) + 2) (I records.length) := by
    refine Hs.loopN (c := .eq t0 v1) (show t0 ≠ v1 by decide) I records.length (12 * W + 20) ?_ ?_
    · intro k hk b ⟨hbcount, hbmarker, hbi, hbo, hbram, hbrc, hbkin, hbkout, hbkc, hbc, hbf⟩
      refine ⟨by simp [Cnd.eval, hbmarker, hk, hbc.one], ?_⟩
      have hinput : C.inp.drop (a.ip + k * (2 * W + 1)) =
          frame (binary W records[k]) ++ (nativeFamilyPacket W (records.drop (k + 1)) ++ suffix) := by
        rw [← List.drop_drop, hin, List.drop_append_of_le_length (by rw [nativeFamilyPacket_length]; nlinarith),
          nativeFamilyPacket_offset W records k hk.le, List.drop_eq_getElem_cons hk, nativeFamilyPacket_cons,
          List.append_assoc]
      have hprevious : b.ram familyRecordStore = records.take k := by rw [hbram]; simp
      have hpreviousCursor : b.rc familyRecordStore = (records.take k).length := by
        rw [hbrc]
        simp [List.length_take, min_eq_left hk.le]
      refine (familyPacketStepProgram_spec C b hbc W records[k] (a.ip + k * (2 * W + 1)) k
        (records.drop (k + 1)) suffix (records.take k) hWpos hW
        (hfit _ (List.getElem_mem hk)) hbi hinput hprevious hpreviousCursor hbcount
        (by omega)).mono le_rfl ?_
      rintro d ⟨hdcount, hdmarker, hdi, hdo, hdram, hdrc, hdkin, hdkout, hdkc, hdc, hdf⟩
      refine ⟨hdcount, ?_, ?_, hdo.trans hbo, ?_, ?_, hdkin.trans hbkin,
        hdkout.trans hbkout, hdkc.trans hbkc, hdc, Fr.trans hbf hdf⟩
      · by_cases hk' : k + 1 < records.length
        · have hne : records.drop (k + 1) ≠ [] := by
            simp only [ne_eq, List.drop_eq_nil_iff]
            omega
          simpa [hne, hk'] using hdmarker
        · have he : records.drop (k + 1) = [] := List.drop_eq_nil_iff.mpr (by omega)
          simpa [he, hk'] using hdmarker
      · rw [hdi]
        ring
      · rw [hdram, hbram]
        rw [List.take_succ_eq_append_getElem hk]
        simp
      · rw [hdrc, hbrc]
        simp [List.length_take, min_eq_left hk.le]
    · intro b ⟨_, hbmarker, _, _, _, _, _, _, _, hbc, _⟩
      simp [Cnd.eval, hbmarker, hbc.one]
  unfold loadFamilyPacketProgram
  refine (Hs.seq (t2 := 1 + (records.length * (12 * W + 22) + 2) + 1)
    (hs_zero C cacheCountVar a) fun b hb => ?_).mono (by omega) (fun _ h => h)
  subst b
  let start := a.set cacheCountVar 0
  have hstartc : Cst start := Cst.of_fr (T := [cacheCountVar]) hc (Fr.set _ _ (by decide)) (by decide)
  refine Hs.seq (t2 := records.length * (12 * W + 22) + 2)
    (readFamilyMarkerProgram_spec C start hstartc W records suffix hWpos hin)
    fun b ⟨hbmarker, hbi, hbr, hbc, hbf⟩ => ?_
  simp only [Prod.mk.injEq] at hbr
  obtain ⟨hbo, hbram, hbrc, hbkin, hbkout, hbkc⟩ := hbr
  have hram0 : Function.update a.ram familyRecordStore ([] : List ℕ) = a.ram := by
    funext m
    by_cases hm : m = familyRecordStore
    · subst m; simp [hstore]
    · simp [Function.update_of_ne hm]
  have hrc0 : Function.update a.rc familyRecordStore 0 = a.rc := by
    funext m
    by_cases hm : m = familyRecordStore
    · subst m; simp [hcursor]
    · simp [Function.update_of_ne hm]
  have hinit : I 0 b := by
    refine ⟨?_, ?_, by simpa [start] using hbi, hbo, ?_, ?_, hbkin, hbkout, hbkc, hbc, ?_⟩
    · rw [hbf _ (by decide)]
      exact DS.set_env_self a cacheCountVar 0
    · by_cases he : records = []
      · simpa [he] using hbmarker
      · have hp : 0 < records.length := List.length_pos_iff.mpr he
        simpa [he, hp] using hbmarker
    · simpa only [List.take_zero, hram0, start, DS.set_ram] using hbram
    · simpa only [hrc0, start, DS.set_rc] using hbrc
    · exact Fr.trans (Fr.set _ _ (by simp [familyPacketScratch])) (Fr.weaken hbf (by decide))
  refine (hloop b hinit).mono le_rfl ?_
  rintro d ⟨hdcount, hdmarker, hdi, hdo, hdram, hdrc, hdkin, hdkout, hdkc, hdc, hdf⟩
  refine ⟨hdcount, by simpa using hdmarker, ?_, hdo, by simpa only [List.take_length] using hdram,
    hdrc, hdkin, hdkout, hdkc, hdc, hdf⟩
  rw [nativeFamilyPacket_length]
  omega

end NearQuarticWires.StageRecovery
