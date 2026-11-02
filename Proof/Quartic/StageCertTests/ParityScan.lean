import Proof.Quartic.StageCertTests.PatternParity
import Proof.Gates.Cells.Kit

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertTests

open NearCubicGates.Close.Cells

/-- `sec:cycle`, paper/paper.tex:
the original eight-bit sign ordinal is retained outside scan scratch. -/
def signOrdinal : Fin VV := ⟨68,by decide⟩
/-- `sec:cycle`, paper/paper.tex: remaining sign bits. -/
def signCode : Fin VV := ⟨69,by decide⟩
/-- `sec:cycle`, paper/paper.tex: scanned true-bit count. -/
def signSum : Fin VV := ⟨70,by decide⟩
/-- `sec:cycle`, paper/paper.tex: next literal sign bit. -/
def signBit : Fin VV := ⟨71,by decide⟩
/-- `sec:cycle`, paper/paper.tex: remaining-bit quotient. -/
def signQuotient : Fin VV := ⟨72,by decide⟩
/-- `sec:cycle`, paper/paper.tex: nonzero-κ flag. -/
def signActive : Fin VV := ⟨73,by decide⟩

/-- `sec:cycle`, paper/paper.tex:
one actual binary division removes the next sign bit and adds its value. -/
def parityStep : St VV MM :=
  .seq (.op (.dm signCode v2 signQuotient signBit))
    (.seq (.op (.copy signCode signQuotient)) (.op (.add signSum signBit)))

/-- `sec:cycle`, paper/paper.tex:
the physical bit scan preserves original source streams and all
registers outside its explicit constant-size scratch set. -/
theorem parityStep_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (code acc : ℕ) (hcode : a.env signCode = code) (hacc : a.env signSum = acc)
    (hfour : 4 ≤ 2 ^ C.Wd) (hfit : acc+1 < 2 ^ C.Wd) :
    Hs C parityStep a 5 (fun b => b.env signCode = code/2 ∧
      b.env signSum = acc+code%2 ∧ b.sh = a.sh ∧
      Fr a b [signCode,signSum,signBit,signQuotient]) := by
  unfold parityStep
  refine Hs.seq (t2 := 3) (hs_dm C signCode v2 signQuotient signBit a
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [hc.two];norm_num) (by rw [hc.two];exact hfour)) fun b hb => ?_
  subst b
  refine Hs.seq (t2 := 1) (hs_copy C signCode signQuotient _ (by decide)) fun b hb => ?_
  subst b
  refine (hs_add C signSum signBit _ (by decide) (by
    simp (config := {decide := true}) [DS.set,hacc,hcode,hc.two]
    have := Nat.mod_lt code (by decide : 0<2)
    omega)).mono le_rfl ?_
  rintro b rfl
  refine ⟨?_,?_,rfl,?_⟩
  · simp (config := {decide := true}) [DS.set,hcode,hc.two]
  · simp (config := {decide := true}) [DS.set,hacc,hcode,hc.two]
  · exact Fr.trans (Fr.set _ _ (by decide))
      (Fr.trans (Fr.set _ _ (by decide))
        (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide))))

/-- `sec:cycle`, paper/paper.tex:
a fixed finite bit scan is a literal finite program, without a
data-dependent exponential loop. -/
def parityScan : ℕ → St VV MM
  | 0 => skipS
  | n+1 => .seq parityStep (parityScan n)

/-- `sec:cycle` and `prop:time`, paper/paper.tex: the exact low-bit scan takes six source operations
per bit and retains its original ordinal outside scratch. -/
theorem parityScan_spec (n : ℕ) (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (code acc : ℕ) (hcode : a.env signCode = code) (hacc : a.env signSum = acc)
    (hfour : 4 ≤ 2 ^ C.Wd) (hfit : acc+n < 2 ^ C.Wd) :
    Hs C (parityScan n) a (6*n+1) (fun b => b.env signCode = code/2^n ∧
      b.env signSum = acc+lowerBitSum n code ∧ b.sh = a.sh ∧
      Fr a b [signCode,signSum,signBit,signQuotient,vJ]) := by
  induction n generalizing a code acc with
  | zero =>
    refine (skip_spec (C := C) a).mono (by norm_num) ?_
    rintro b rfl
    exact ⟨by simpa (config := {decide := true}) [DS.set] using hcode,
      by simpa (config := {decide := true}) [DS.set,lowerBitSum] using hacc,rfl,Fr.set _ _ (by decide)⟩
  | succ n ih =>
    unfold parityScan
    refine (Hs.seq (t2 := 6*n+1) (parityStep_spec C a hc code acc hcode hacc hfour (by omega))
      fun b ⟨hbc,hba,hbs,hbf⟩ => ?_).mono (by ring_nf;omega) (fun _ h => h)
    have hconst : Cst b := Cst.of_fr hc hbf (by decide)
    have hnext : acc+code%2+n < 2 ^ C.Wd := by
      have := Nat.mod_lt code (by decide : 0<2)
      omega
    refine (ih b hconst (code/2) (acc+code%2) hbc hba hnext).mono le_rfl ?_
    rintro d ⟨hdc,hda,hds,hdf⟩
    refine ⟨?_,?_,hds.trans hbs,Fr.trans (Fr.weaken hbf (by decide)) hdf⟩
    · rw [hdc,Nat.div_div_eq_div_mul,pow_succ]
      congr 1
      omega
    · rw [hda]
      simp only [lowerBitSum,Nat.add_assoc]

end NearQuarticWires.StageCertTests
