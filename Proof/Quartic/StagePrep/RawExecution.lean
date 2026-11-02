import Proof.Quartic.StagePrep.CanonicalExit
import Proof.Quartic.StagePrep.RawCost

/-!
# All original preparation requests

Paper: normalized calls in `thm:counter`, paper/paper.tex, and `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open NearCubicGates.Close.Interfaces
open Classical

/-- The literal raw program of `prop:time`,
paper/paper.tex, emits the complete exact
preparation word on every original call and every witness.
Its setup and all branch costs are independent of the unread
witness suffix. -/
theorem rawPreparationProgram_spec (C : Ctx) (B1 B2 : ℕ) (c : Call)
    (hcw : C.cw=callWord c)
    (hW : 2*C.cw.length+8 ≤ C.Wd)
    (hL : 2*C.cw.length+4<2^C.Wd)
    (hA : (B1+B2+5)*((callWord c).length+1) ≤ C.Wd)
    (hwidth : 100*Cells.ParameterArithmetic.preparationBitBase B1 (callWord c).length ≤ C.Wd) :
    Hs C (rawPreparationProgram B1 B2) a0 (rawPreparationCost B1 B2 C.Wd c)
      (fun b => b.out=Program.prepWord B1 B2 c C.wit ∧ Cst b ∧
        b.wq ≤ 5*(c.n+1)^5) := by
  have hv0 : Valid C (a0 (V:=VV)) := by
    refine ⟨?_,by simp [a0],by simp [a0]⟩
    intro v
    exact Nat.pow_pos (by decide)
  unfold rawPreparationProgram
  refine Hx.hs (Hs.then (Hs.addValid (by omega) hv0
    (preparationFront_spec C B1 B2 c hcw hW hL hA))
    (fun a ⟨⟨hparse,hadm,hcount,_,_,hwq,hout,hc⟩,hv⟩ n1 hn1 => ?_))
  by_cases ha : Transfer.Admitted4 B1 B2 c
  · have ha1 : a.env vADM=1 := by rw [hadm]; exact bnat_one_of ha
    by_cases hz : Transfer.callWires c=0
    · refine Hs.last (Hs.iteT (show vADM≠v1 by decide) (by simp [Cnd.eval,ha1,hc.one])
        (Hs.iteT (show censusTotal≠vZ by decide) (by simp [Cnd.eval,hcount,hz,hc.z])
          (closedZeroOutput_prepWord_spec C B1 B2 c C.wit ha hz a hc hparse hcw hW
            (by omega)))) ?_
      rintro b ⟨hbout,hbc,hbwq,_⟩ n2 hn2
      refine ⟨⟨?_,hbc,?_⟩,?_⟩
      · simpa only [hout,List.nil_append] using hbout
      · rw [hbwq,hwq]; exact Nat.zero_le _
      · simp only [rawPreparationCost,if_pos ha,if_pos hz]
        rw [hcw] at hn1 hn2
        omega
    · refine Hs.last (Hs.iteT (show vADM≠v1 by decide) (by simp [Cnd.eval,ha1,hc.one])
        (Hs.iteF (show censusTotal≠vZ by decide) (by simp [Cnd.eval,hcount,hc.z,hz])
          (canonicalExit_spec C B1 B2 c a hc hv hparse ha hz hcw ha1 hcount hwq hwidth))) ?_
      rintro b ⟨hbout,hbc,hbwq⟩ n2 hn2
      refine ⟨⟨?_,hbc,hbwq⟩,?_⟩
      · simpa only [hout,List.nil_append] using hbout
      · simp only [rawPreparationCost,if_pos ha,if_neg hz]
        rw [hcw] at hn1
        omega
  · have ha0 : a.env vADM=0 := by rw [hadm]; exact bnat_zero_of_not ha
    refine Hs.last (Hs.iteF (show vADM≠v1 by decide) (by simp [Cnd.eval,ha0,hc.one])
      (defaultPreparationOutput_not_admitted C B1 B2 c C.wit ha a hc)) ?_
    rintro b ⟨hbout,_,hbwq,hbc,_⟩ n2 hn2
    refine ⟨⟨?_,hbc,?_⟩,?_⟩
    · simpa only [hout,List.nil_append] using hbout
    · rw [hbwq,hwq]; exact Nat.zero_le _
    · simp only [rawPreparationCost,if_neg ha]
      rw [hcw] at hn1
      have hdlen : defaultPreparationWord.length ≤ 25 := by
        simpa only [defaultPreparationWord,List.length_cons] using
          Nat.add_le_add_right Cells.soundDefault_outputWord_length 1
      have hdef : 2*defaultPreparationWord.length+3 ≤ 200 := by omega
      omega

end NearQuarticWires.StagePrep
