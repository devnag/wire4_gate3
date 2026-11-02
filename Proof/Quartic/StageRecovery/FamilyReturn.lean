import Proof.Quartic.StageRecovery.FamilyPacketLoad
import Proof.Quartic.StageRecovery.FixedField

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: original token length
is saved before computing the one-time appended-family return distance. -/
def savedTokenLengthVar : Fin VV := ⟨117, by decide⟩
/-- `lem:print`, paper/paper.tex: each native family
record's physical frame span is computed from its original binary width. -/
def familyRecordSpanVar : Fin VV := ⟨118, by decide⟩
/-- `lem:print`, paper/paper.tex: the actual computed
record count is multiplied by its physical frame span. -/
def familyPacketSpanVar : Fin VV := ⟨119, by decide⟩

/-- `lem:print`, paper/paper.tex: the complete return
distance is computed by actual binary operations from serialized L,
original field width W and the physically parsed record count N. -/
def computeFamilySpanProgram : St VV MM :=
  .seq (.op (.copy savedTokenLengthVar tokenLengthVar))
    (.seq (.op (.copy familyRecordSpanVar FixedBits.width))
      (.seq (.op (.shl familyRecordSpanVar))
        (.seq (.op (.inc familyRecordSpanVar))
          (.seq (.op (.mul cacheCountVar familyRecordSpanVar familyPacketSpanVar))
            (.seq (.op (.copy tokenLengthVar familyPacketSpanVar))
              (.seq (.op (.add tokenLengthVar savedTokenLengthVar)) (.op (.inc tokenLengthVar))))))))

/-- `lem:print`, paper/paper.tex: only the declared
four binary work registers change while computing the paid return span. -/
def familySpanScratch : List (Fin VV) :=
  [savedTokenLengthVar, familyRecordSpanVar, familyPacketSpanVar, tokenLengthVar]

/-- `lem:print`, paper/paper.tex: the literal binary
span computation includes the native packet's final delimiter and uses
the actual parsed count, with no output-length observation. -/
theorem computeFamilySpanProgram_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (L W N : ℕ) (hL : a.env tokenLengthVar = L) (hW : a.env FixedBits.width = W)
    (hN : a.env cacheCountVar = N) (hspan : 2 * W + 1 < 2 ^ C.Wd)
    (hfit : L + N * (2 * W + 1) + 1 < 2 ^ C.Wd) :
    Hs C computeFamilySpanProgram a 15 (fun b =>
      b.env tokenLengthVar = L + N * (2 * W + 1) + 1 ∧
      b.env savedTokenLengthVar = L ∧ b.sh = a.sh ∧ Cst b ∧ Fr a b familySpanScratch) := by
  unfold computeFamilySpanProgram
  refine Hs.seq (t2 := 13) (hs_copy C savedTokenLengthVar tokenLengthVar a (by decide)) fun b hb => ?_
  subst b
  refine Hs.seq (t2 := 11) (hs_copy C familyRecordSpanVar FixedBits.width _ (by decide)) fun b hb => ?_
  subst b
  refine Hs.seq (t2 := 9) (hs_shl C familyRecordSpanVar _
    (by simp (config := {decide := true}) [DS.set, hW]; omega)) fun b hb => ?_
  subst b
  refine Hs.seq (t2 := 7) (hs_inc C familyRecordSpanVar _
    (by simpa (config := {decide := true}) [DS.set, hW] using hspan)) fun b hb => ?_
  subst b
  refine Hs.seq (t2 := 5) (hs_mul C cacheCountVar familyRecordSpanVar familyPacketSpanVar _
    (by decide) (by decide) (by decide)
    (by simp (config := {decide := true}) [DS.set, hN, hW]; omega)) fun b hb => ?_
  subst b
  refine Hs.seq (t2 := 3) (hs_copy C tokenLengthVar familyPacketSpanVar _ (by decide)) fun b hb => ?_
  subst b
  refine Hs.seq (t2 := 1) (hs_add C tokenLengthVar savedTokenLengthVar _ (by decide)
    (by simp (config := {decide := true}) [DS.set, hN, hW, hL]; omega)) fun b hb => ?_
  subst b
  refine (hs_inc C tokenLengthVar _
    (by simpa (config := {decide := true}) [DS.set, hN, hW, hL, Nat.add_comm] using hfit)).mono le_rfl ?_
  rintro b rfl
  refine ⟨by simp (config := {decide := true}) [DS.set, hN, hW, hL, Nat.add_comm],
    by simp (config := {decide := true}) [DS.set, hL], rfl, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩ <;>
      simp (config := {decide := true}) [DS.set, hc.z, hc.one, hc.two]
  · intro y hy
    simp only [familySpanScratch, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp only [DS.set, Function.update_of_ne hy.1, Function.update_of_ne hy.2.1,
      Function.update_of_ne hy.2.2.1, Function.update_of_ne hy.2.2.2]

/-- `lem:print`, paper/paper.tex: one actual return
crosses the original tokens and parsed native packet, then restores L
for each later cached Formula evaluation. -/
def returnFromFamilyProgram : St VV MM :=
  .seq computeFamilySpanProgram
    (.seq inputReturnProgram (.op (.copy tokenLengthVar savedTokenLengthVar)))

/-- `lem:print`, paper/paper.tex: the one-time native
family join pays exactly its linear physical return distance and
restores the retained Formula's original token cursor and length. -/
theorem returnFromFamilyProgram_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (L W N base : ℕ) (hL : a.env tokenLengthVar = L) (hW : a.env FixedBits.width = W)
    (hN : a.env cacheCountVar = N) (hspan : 2 * W + 1 < 2 ^ C.Wd)
    (hfit : L + N * (2 * W + 1) + 1 < 2 ^ C.Wd)
    (hip : a.ip = base + (L + N * (2 * W + 1) + 1)) :
    Hs C returnFromFamilyProgram a (5 * (L + N * (2 * W + 1) + 1) + 22) (fun b =>
      b.ip = base ∧ b.env tokenLengthVar = L ∧ inputRest b = inputRest a ∧
      Cst b ∧ Fr a b (inputReturnIndex :: familySpanScratch)) := by
  unfold returnFromFamilyProgram
  refine (Hs.seq (t2 := (5 * (L + N * (2 * W + 1) + 1) + 4) + 1 + 1)
    (computeFamilySpanProgram_spec C a hc L W N hL hW hN hspan hfit)
    fun b ⟨hbl, hbs, hbsh, hbc, hbf⟩ => ?_).mono (by omega) (fun _ h => h)
  have hbi : b.ip = a.ip := (Same.of_sh hbsh).ip
  refine Hs.seq (t2 := 1) (inputReturnProgram_spec C b _ base hbl (hbi.trans hip) hfit)
    fun d ⟨hdi, hdr, hdf⟩ => ?_
  refine (hs_copy C tokenLengthVar savedTokenLengthVar d (by decide)).mono le_rfl ?_
  rintro e rfl
  have hfr : Fr a (d.set tokenLengthVar (d.env savedTokenLengthVar)) (inputReturnIndex :: familySpanScratch) :=
    Fr.trans (Fr.weaken hbf (by intro y hy; simp [hy]))
      (Fr.trans (Fr.weaken hdf (by simp)) (Fr.set _ _ (by decide)))
  exact ⟨hdi, by rw [DS.set_env_self, hdf _ (by decide), hbs],
    hdr.trans (by have hs := Same.of_sh hbsh; simp [inputRest, formulaRest, hs.out, hs.ram, hs.rc, hs.kin, hs.kout, hs.kc]),
    Cst.of_fr hc hfr (by decide), hfr⟩

end NearQuarticWires.StageRecovery
