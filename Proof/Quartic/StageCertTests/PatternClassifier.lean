import Proof.Quartic.StageCertTests.ParityScan

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertTests

open NearCubicGates.Close.Cells

/-- `sec:cycle`, paper/paper.tex:
the literal eight-bit classifier scans the ordinal, computes parity,
and retains exactly the sign patterns whose integer weight is nonzero. -/
def classifySignPattern : St VV MM :=
  .seq (.op (.copy signCode signOrdinal)) (.seq (.op (.zero signSum))
    (.seq (parityScan 8) (.seq (.op (.dm signSum v2 signQuotient signBit))
      (.ite (.eq signBit vZ)
        (.seq (.op (.zero signActive)) (.op (.inc signActive)))
        (.op (.zero signActive))))))

/-- `sec:cycle` and `prop:time`, paper/paper.tex: a fixed physical program decides the exact nonzero-κ
condition in constant source time, preserving its ordinal and all streams. -/
theorem classifySignPattern_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (code : Fin 256) (hcode : a.env signOrdinal = code.val) (hfour : 4 ≤ 2 ^ C.Wd)
    (hroom : 8 < 2 ^ C.Wd) :
    Hs C classifySignPattern a 64 (fun b =>
      b.env signActive = (decide (Cycle.kappa 4 (patternOfCode code.val) ≠ 0)).toNat ∧
      b.env signOrdinal = code.val ∧ b.sh = a.sh ∧
      Fr a b [signCode,signSum,signBit,signQuotient,signActive,vJ]) := by
  unfold classifySignPattern
  refine (Hs.seq (t2 := 62) (hs_copy C signCode signOrdinal a (by decide))
    fun b hb => ?_).mono (by omega) (fun _ h => h)
  subst b
  refine (Hs.seq (t2 := 59) (hs_zero C signSum _) fun b hb => ?_).mono (by omega) (fun _ h => h)
  subst b
  let start := (a.set signCode (a.env signOrdinal)).set signSum 0
  have hsc : Cst start := Cst.of_fr (T := [signCode,signSum]) hc
    (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide))) (by decide)
  have hstep := parityScan_spec 8 C start hsc code.val 0
    (by simp (config := {decide := true}) [start,DS.set,hcode]) (by simp [start]) hfour (by simpa using hroom)
  refine (Hs.seq (t2 := 9) hstep fun b ⟨_,hbsum,hbsh,hbfr⟩ => ?_).mono (by norm_num) (fun _ h => h)
  have hbc : Cst b := Cst.of_fr hsc hbfr (by decide)
  have hsum : b.env signSum = lowerBitSum 8 code.val := by simpa using hbsum
  refine (Hs.seq (t2 := 6) (hs_dm C signSum v2 signQuotient signBit b
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [hbc.two];norm_num) (by rw [hbc.two];exact hfour)) fun d hd => ?_).mono (by omega) (fun _ h => h)
  subst d
  let base := (b.set signQuotient (b.env signSum/b.env v2)).set signBit (b.env signSum%b.env v2)
  have heven : base.env signBit = lowerBitSum 8 code.val % 2 := by simp [base,hsum,hbc.two]
  have hzero : base.env vZ = 0 := by simp (config := {decide := true}) [base,DS.set,hbc.z]
  have hpost (d : DS VV MM) (hf : Fr b d [signQuotient,signBit,signActive])
      (hs : d.sh = b.sh)
      (ha : d.env signActive = (decide (lowerBitSum 8 code.val%2=0)).toNat) :
      d.env signActive = (decide (Cycle.kappa 4 (patternOfCode code.val) ≠ 0)).toNat ∧
      d.env signOrdinal = code.val ∧ d.sh = a.sh ∧
      Fr a d [signCode,signSum,signBit,signQuotient,signActive,vJ] := by
    refine ⟨?_,?_,hs.trans hbsh,?_⟩
    · rw [ha,kappa_patternOfCode]
    · rw [hf _ (by decide),hbfr _ (by decide)]
      simp (config := {decide := true}) [start,DS.set,hcode]
    · exact Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide))
        (Fr.trans (Fr.weaken hbfr (by decide)) (Fr.weaken hf (by decide))))
  change Hs C (.ite (.eq signBit vZ) _ _) base 6 _
  refine Hs.ite (show signBit ≠ vZ by decide) (fun ht => ?_) (fun ht => ?_)
  · have hpar : lowerBitSum 8 code.val % 2=0 := by
      simpa only [Cnd.eval,heven,hzero,decide_eq_true_eq] using ht
    refine (Hs.seq (t2 := 1) (hs_zero C signActive base) fun d hd => ?_).mono (by omega) (fun _ h => h)
    subst d
    refine (hs_inc C signActive _ (by simp only [DS.set_env_self];omega)).mono le_rfl ?_
    rintro d rfl
    apply hpost
    · exact Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide))
        (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide))))
    · rfl
    · simp [hpar]
  · have hpar : ¬lowerBitSum 8 code.val % 2=0 := by
      simpa only [Cnd.eval,heven,hzero,decide_eq_false_iff_not] using ht
    refine (hs_zero C signActive base).mono (by omega) ?_
    rintro d rfl
    apply hpost
    · exact Fr.trans (Fr.set _ _ (by decide))
        (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide)))
    · rfl
    · simp [hpar]

end NearQuarticWires.StageCertTests
