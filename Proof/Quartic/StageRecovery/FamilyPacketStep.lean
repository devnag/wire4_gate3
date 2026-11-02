import Proof.Quartic.StageRecovery.FamilyPacket

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: after observing a
true marker, the actual packet parser returns one cell, loads its whole
record, increments the computed count and reads the next marker. -/
def familyPacketStepProgram : St VV MM :=
  .seq (.op .bkI)
    (.seq loadFamilyRecordProgram (.seq (.op (.inc cacheCountVar)) readFamilyMarkerProgram))

/-- `lem:print`, paper/paper.tex: the finite packet
parser keeps its record counter separate from every original header field. -/
def familyPacketScratch : List (Fin VV) := cacheCountVar :: familyLoadScratch

/-- `lem:print`, paper/paper.tex: one actual parsing
step consumes exactly one complete native frame and its next marker,
appends the original record and derives the next exact record count. -/
theorem familyPacketStepProgram_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (W value base count : ℕ) (records : List ℕ) (suffix : List Bool) (previousRecords : List ℕ)
    (hWpos : 0 < W) (hW : W + 2 ≤ C.Wd) (hvalue : value < 2 ^ W)
    (hip : a.ip = base + 1)
    (hin : C.inp.drop base = frame (binary W value) ++ (nativeFamilyPacket W records ++ suffix))
    (hstore : a.ram familyRecordStore = previousRecords)
    (hcursor : a.rc familyRecordStore = previousRecords.length)
    (hcount : a.env cacheCountVar = count) (hcountfit : count + 1 < 2 ^ C.Wd) :
    Hs C familyPacketStepProgram a (12 * W + 20) (fun b =>
      b.env cacheCountVar = count + 1 ∧ b.env t0 = (decide (records ≠ [])).toNat ∧
      b.ip = base + (2 * W + 1) + 1 ∧ b.out = a.out ∧
      b.ram = Function.update a.ram familyRecordStore (previousRecords ++ [value]) ∧
      b.rc = Function.update a.rc familyRecordStore (previousRecords.length + 1) ∧
      b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧ Cst b ∧ Fr a b familyPacketScratch) := by
  unfold familyPacketStepProgram
  refine (Hs.seq (t2 := 12 * W + 18) (Hs.op (OpEx.bkI (C := C) a (by omega)) rfl) fun b hb => ?_).mono (by omega) (fun _ h => h)
  subst b
  let start : DS VV MM := { a with ip := base }
  have hs : ({ a with ip := a.ip - 1 } : DS VV MM) = start := by
    dsimp [start]
    congr 1
    omega
  rw [hs]
  have hstartc : Cst start := ⟨hc.z, hc.one, hc.two⟩
  refine Hs.seq (t2 := 3) (loadFamilyRecordProgram_spec C start hstartc W value _ previousRecords
    hin hvalue hW hstore hcursor) fun b ⟨hbi, hbo, hbram, hbrc, hbkin, hbkout, hbkc, hbc, hbf⟩ => ?_
  have hbcounter : b.env cacheCountVar = count := by
    rw [hbf _ (by decide)]
    exact hcount
  refine Hs.seq (t2 := 1) (hs_inc C cacheCountVar b (by rw [hbcounter]; exact hcountfit)) fun d hd => ?_
  subst d
  let d := b.set cacheCountVar (count + 1)
  have hd : b.set cacheCountVar (b.env cacheCountVar + 1) = d := by rw [hbcounter]
  rw [hd]
  have hdc : Cst d := Cst.of_fr (T := [cacheCountVar]) hbc (Fr.set _ _ (by decide)) (by decide)
  have hdi : d.ip = base + (2 * W + 1) := hbi
  have hinput : C.inp.drop d.ip = nativeFamilyPacket W records ++ suffix := by
    rw [hdi, ← List.drop_drop, hin]
    have hlen : (frame (binary W value)).length = 2 * W + 1 := by
      rw [frame_length, SignedSortKey.binary_length]
    rw [← hlen, List.drop_left]
  refine (readFamilyMarkerProgram_spec C d hdc W records suffix hWpos hinput).mono le_rfl ?_
  rintro e ⟨hemarker, hei, her, hec, hef⟩
  simp only [Prod.mk.injEq] at her
  obtain ⟨heo, heram, herc, hekin, hekout, hekc⟩ := her
  refine ⟨?_, hemarker, by rw [hei, hdi], heo.trans hbo, heram.trans hbram,
    herc.trans hbrc, hekin.trans hbkin, hekout.trans hbkout, hekc.trans hbkc, hec, ?_⟩
  · rw [hef _ (by decide)]
    exact DS.set_env_self b cacheCountVar (count + 1)
  · have hf0 : Fr a start familyPacketScratch := fun _ _ => rfl
    exact Fr.trans hf0 (Fr.trans (Fr.weaken hbf (by intro y hy; simp [familyPacketScratch, hy]))
      (Fr.trans (Fr.set _ _ (by simp [familyPacketScratch])) (Fr.weaken hef (by decide))))

end NearQuarticWires.StageRecovery
