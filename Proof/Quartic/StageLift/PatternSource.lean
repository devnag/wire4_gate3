import Proof.Quartic.StageLift.RecordCopy
import Proof.Quartic.StageLift.PatternCode
import Proof.Quartic.StageLift.GammaStart

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

/-- Step 3, `sec:algorithm`, paper/paper.tex: only eight original
pattern records are retained for the fixed-width binary-prefix reader. -/
def patternStore : Fin MM := 8
def signCodeVar : Fin VV := 71
def callKindVar : Fin VV := 72

/-- Step 3, `sec:algorithm`, paper/paper.tex: the signed side and
eight sign bits are read from their actual normalized index records. -/
def retainPrintPattern : St VV MM :=
  .seq loadPrintPart (copyRecords indexStore patternStore 8)

/-- Step 3, `sec:algorithm`, paper/paper.tex: finite sign retention
copies exactly eight real records and pays the original index head return. -/
theorem retainPrintPattern_spec {B1 B2 : ℕ} (C : Ctx) (r : Greedy.PrintRequest B1 B2)
    (a : DS VV MM) (hc : Cst a) (hindex : a.ram indexStore = normalizedPrintIndex r)
    (hempty : a.ram patternStore = [] ∧ a.rc patternStore = 0) :
    Hs C retainPrintPattern a (a.rc indexStore + 37) (fun b =>
      b.env partVar = r.sign.toNat ∧
      b.ram patternStore = (List.ofFn r.pattern).map Bool.toNat ∧
      b.rc patternStore = 8 ∧ b.rc indexStore = 9 ∧
      (∀ store, store ≠ patternStore → b.ram store = a.ram store) ∧
      (∀ store, store ≠ indexStore → store ≠ patternStore → b.rc store = a.rc store) ∧
      (b.ip, b.out, b.kin, b.kout, b.kc) = (a.ip, a.out, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b [partVar, t1, vJ]) := by
  let bits := (List.ofFn r.pattern).map Bool.toNat
  let tail := [r.prime] ++ (printDigitList r ++ printResidueList r).map
    (fun z : ℤ => (z % (r.prime ^ r.child.selected.1.e : ℤ)).toNat)
  have hword : a.ram indexStore = r.sign.toNat :: (bits ++ tail) := by
    rw [hindex]
    simp only [normalizedPrintIndex, bits, tail, List.cons_append, List.nil_append, List.append_assoc]
  unfold retainPrintPattern
  refine Hs.seq (t2 := 33) (loadPrintPart_spec C r.sign (bits ++ tail) a hc hword)
    fun b ⟨hbp, hbrc, hbram, hbsh, hbc, hbf⟩ => ?_
  have hbin : (b.ram indexStore).drop (b.rc indexStore) = bits ++ tail := by
    rw [hbram, hbrc, Function.update_self, hword]
    rfl
  have hbempty : b.ram patternStore = [] ∧ b.rc patternStore = 0 := by
    rw [hbram, hbrc, Function.update_of_ne (by decide)]
    exact hempty
  have hs := copyRecords_spec C indexStore patternStore (by decide) bits tail b hbc hbin
    (by rw [hbempty.1, hbempty.2]; rfl)
  have hlen : bits.length = 8 := print_pattern_length r
  rw [hlen] at hs
  refine hs.mono le_rfl ?_
  rintro d ⟨hdram, hdrc, hdsource, hdo, hdcur, hdsh, hdc, hdf⟩
  refine ⟨?_, by simpa only [hbempty.1, List.nil_append] using hdram,
    by simpa only [hbempty.2, zero_add] using hdrc, ?_, ?_, ?_, hdsh.trans hbsh, hdc, ?_⟩
  · rw [hdf partVar (by decide)]
    exact hbp
  · rw [hdsource, hbrc, Function.update_self]
  · intro store hs
    rw [hdo store hs, hbram]
  · intro store hi hp
    rw [hdcur store hi hp, hbrc, Function.update_of_ne hi]
  · exact (hbf.weaken (by simp)).trans (hdf.weaken (by simp))

/-- Step 3 and `lem:print`, paper/paper.tex: reuse the checked physical binary-prefix loop on the
eight actually retained sign records, before the geometric header phase. -/
def decodePrintPattern : St VV MM :=
  .seq (setK StagePrint.Header.count 8)
    (.seq (.op (.zero StagePrint.Header.translation))
      (.seq (.op (.copy StagePrint.Header.power v1))
        (.seq (StagePrint.Header.translationLoop patternStore)
          (.op (.copy signCodeVar StagePrint.Header.translation)))))

/-- Step 3 and `lem:print`, paper/paper.tex: actual pattern records determine the exact code used by
every subsequent original signed linear-form replay. -/
theorem decodePrintPattern_spec (C : Ctx) (pattern : Cycle.SignPattern 4)
    (a : DS VV MM) (hc : Cst a)
    (hmem : a.ram patternStore = (List.ofFn pattern).map Bool.toNat)
    (hcap : 256 < 2 ^ C.Wd) :
    Hs C decodePrintPattern a
      (StagePrint.Header.translationCost (a.rc patternStore) 8 + 26) (fun b =>
      b.env signCodeVar = printPatternCode pattern ∧ b.ram = a.ram ∧
      (b.ip, b.out, b.kin, b.kout, b.kc) = (a.ip, a.out, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b [StagePrint.Header.count, StagePrint.Header.translation,
        StagePrint.Header.power, StagePrint.Header.index, c0, vJ, t1, t3, signCodeVar]) := by
  unfold decodePrintPattern
  apply Hx.hs
  refine Hs.then (setK_spec StagePrint.Header.count (by decide) 8 a (by omega))
    (fun b ⟨hb8, hbsh, hbfr⟩ n1 hn1 => ?_)
  refine Hs.then (hs_zero C StagePrint.Header.translation b) (fun d hd n2 hn2 => ?_)
  subst d
  let s1 := b.set StagePrint.Header.translation 0
  refine Hs.then (hs_copy C StagePrint.Header.power v1 s1 (by decide))
    (fun d hd n3 hn3 => ?_)
  subst d
  let s2 := s1.set StagePrint.Header.power (s1.env v1)
  have hf2 : Fr a s2 [StagePrint.Header.count, StagePrint.Header.translation, StagePrint.Header.power, vJ] :=
    (hbfr.weaken (by simp)).trans ((Fr.set b _ (by simp)).trans (Fr.set s1 _ (by simp)))
  have hc2 : Cst s2 := Cst.of_fr hc hf2 (by decide)
  have hsame := Same.of_sh hbsh
  have hmem2 : s2.ram patternStore = (List.ofFn pattern).map Bool.toNat := by
    change b.ram patternStore = _
    rw [hsame.ram]
    exact hmem
  have hone : b.env v1 = 1 := (hbfr _ (by decide)).trans hc.one
  have hloop := StagePrint.Header.translationLoop_run C patternStore (List.ofFn pattern) 8 s2 hc2
    hmem2 (by simp) (by dsimp [s2, s1]; vsimp [hb8])
    (by dsimp [s2, s1]; vsimp []) (by dsimp [s2, s1]; vsimp [hone]) hcap
  refine Hs.then hloop (fun d ⟨hdcode, _hdpower, hdi, hdo, hdram, hdcallee, hdc, hdfr⟩ n4 hn4 => ?_)
  refine Hs.last (hs_copy C signCodeVar StagePrint.Header.translation d (by decide))
    (fun z hz n5 hn5 => ?_)
  subst z
  have hf : Fr a (d.set signCodeVar (d.env StagePrint.Header.translation))
      [StagePrint.Header.count, StagePrint.Header.translation,
        StagePrint.Header.power, StagePrint.Header.index, c0, vJ, t1, t3, signCodeVar] :=
    (hf2.weaken (by simp)).trans ((hdfr.weaken (by
      intro x hx
      simp only [StagePrint.Header.translationScratch, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      tauto)).trans (Fr.set _ _ (by simp)))
  refine ⟨⟨?_, hdram.trans hsame.ram, ?_, Cst.of_fr hc hf (by decide), hf⟩, ?_⟩
  · change d.env StagePrint.Header.translation = _
    exact hdcode.trans (binaryPrefix_printPattern pattern)
  · change (d.ip, d.out, d.kin, d.kout, d.kc) = _
    rw [hdi, hdo]
    change (b.ip, b.out, d.kin, d.kout, d.kc) = _
    simp only [Prod.mk.injEq] at hdcallee
    exact Prod.ext hsame.ip (Prod.ext hsame.out
      (Prod.ext (hdcallee.1.trans hsame.kin)
        (Prod.ext (hdcallee.2.1.trans hsame.kout) (hdcallee.2.2.trans hsame.kc))))
  · change n4 ≤ StagePrint.Header.translationCost (b.rc patternStore) 8 at hn4
    rw [hsame.rc] at hn4
    omega

/-- Step 3 and `lem:print`, paper/paper.tex: the reused decoder accesses only the finite pattern store. -/
theorem decodePrintPattern_avoids (store : Fin MM) (hne : store ≠ patternStore) :
    avoidsStore store decodePrintPattern := by
  simp [decodePrintPattern, StagePrint.Header.translationLoop, StagePrint.Header.translationBody,
    fetch, forS, setK, incS, skipS, avoidsStore, avoidsStoreOp, hne]

/-- Step 3, `sec:algorithm`, paper/paper.tex: the complete real
pattern reader retains eight records and decodes their original ordinal. -/
def readPrintPattern : St VV MM := .seq retainPrintPattern decodePrintPattern

/-- Step 3 and `lem:print`, paper/paper.tex: all unrelated source cursors remain at their actual positions
through the complete pattern-retention and binary-decoding program. -/
theorem readPrintPattern_avoids (store : Fin MM) (hi : store ≠ indexStore)
    (hp : store ≠ patternStore) : avoidsStore store readPrintPattern := by
  have hcopy : ∀ n, avoidsStore store (copyRecords indexStore patternStore n) := by
    intro n
    induction n with
    | zero => trivial
    | succ n ih => exact ⟨hi, hp, ih⟩
  exact ⟨⟨⟨hi, hi⟩, hcopy 8⟩, decodePrintPattern_avoids store hp⟩

/-- Step 3 and `lem:print`, paper/paper.tex: the actual normalized index bank supplies the original side
and every original sign bit. Only eight finite records are copied, once,
and original call, parameters, witness and Gamma cursors are preserved. -/
theorem readPrintPattern_spec {B1 B2 : ℕ} (C : Ctx) (r : Greedy.PrintRequest B1 B2)
    (a : DS VV MM) (hc : Cst a) (hindex : a.ram indexStore = normalizedPrintIndex r)
    (hempty : a.ram patternStore = [] ∧ a.rc patternStore = 0) (hcap : 256 < 2 ^ C.Wd) :
    Hs C readPrintPattern a (a.rc indexStore + 1000) (fun b =>
      b.env partVar = r.sign.toNat ∧ b.env signCodeVar = printPatternCode r.pattern ∧
      (∀ store, store ≠ patternStore → b.ram store = a.ram store) ∧
      (∀ store, store ≠ indexStore → store ≠ patternStore → b.rc store = a.rc store) ∧
      (b.ip, b.out, b.kin, b.kout, b.kc) = (a.ip, a.out, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b [partVar, t1, vJ, StagePrint.Header.count, StagePrint.Header.translation,
        StagePrint.Header.power, StagePrint.Header.index, c0, t3, signCodeVar]) := by
  have hs : Hs C readPrintPattern a (a.rc indexStore + 1000) (fun b =>
      b.env partVar = r.sign.toNat ∧ b.env signCodeVar = printPatternCode r.pattern ∧
      (∀ store, store ≠ patternStore → b.ram store = a.ram store) ∧
      (b.ip, b.out, b.kin, b.kout, b.kc) = (a.ip, a.out, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b [partVar, t1, vJ, StagePrint.Header.count, StagePrint.Header.translation,
        StagePrint.Header.power, StagePrint.Header.index, c0, t3, signCodeVar]) := by
    unfold readPrintPattern
    refine (Hs.seq (t2 := 646) (retainPrintPattern_spec C r a hc hindex hempty)
      fun b ⟨hbp, hbram, hbrc, _hbindex, hbo, _hbcur, hbsh, hbc, hbfr⟩ => ?_).mono
        (by omega) (fun _ h => h)
    have hd := decodePrintPattern_spec C r.pattern b hbc hbram hcap
    rw [hbrc] at hd
    norm_num only [StagePrint.Header.translationCost] at hd
    refine hd.mono le_rfl ?_
    rintro d ⟨hdcode, hdram, hdsh, hdc, hdfr⟩
    refine ⟨?_, hdcode, ?_, hdsh.trans hbsh, hdc, ?_⟩
    · exact (hdfr _ (by decide)).trans hbp
    · intro store hp
      rw [hdram]
      exact hbo store hp
    · exact (hbfr.weaken (by simp)).trans (hdfr.weaken (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
        tauto))
  obtain ⟨b, n, he, hn, hbp, hbcode, hbram, hbsh, hbc, hbfr⟩ := hs
  refine ⟨b, n, he, hn, hbp, hbcode, hbram, ?_, hbsh, hbc, hbfr⟩
  intro store hi hp
  exact (avoidsStore_spec he (readPrintPattern_avoids store hi hp)).2

end NearQuarticWires.StageLift
