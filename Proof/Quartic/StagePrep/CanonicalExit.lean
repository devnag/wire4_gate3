import Proof.Quartic.StagePrep.CanonicalCases
import Proof.Quartic.StagePrep.CanonicalExitCost
import Proof.Quartic.StagePrep.OutputFromMemory
import Proof.Quartic.Cells.ParametersDefaultWord

/-!
# Canonical preparation and its exact output exits

Paper: `sec:params`, paper/paper.tex, and
the preparation cost in `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open NearCubicGates.Close.Counter
open NearCubicGates.Close.Interfaces
open Cells.ParameterArithmetic
open Classical

/-- The concrete parameter computation and its two output
exits in `sec:params`, paper/paper.tex. -/
def canonicalExit : St VV := .seq canonicalPreparation
  (.ite (.eq vADM v1) successfulPreparationOutput defaultPreparationOutput)

/-- Both public selection outcomes of `sec:params`,
paper/paper.tex, execute the same actual
canonical instructions and emit exactly `prepWord` on every
witness, using only the proved original-input word width. -/
theorem canonicalExit_spec (C : Ctx) (B1 B2 : ℕ) (c : Call)
    (a : DS VV) (hc : Cst a) (hv : Valid C a) (hparse : ParseOut c a)
    (hadm : Transfer.Admitted4 B1 B2 c) (hW : Transfer.callWires c≠0)
    (hcw : C.cw=callWord c) (ha : a.env vADM=1)
    (hcount : a.env censusTotal=Transfer.callWires c) (hwq : a.wq=0)
    (hwidth : 100*Cells.ParameterArithmetic.preparationBitBase B1 (callWord c).length ≤ C.Wd) :
    Hs C canonicalExit a (canonicalExitCost c C.Wd)
      (fun b => b.out=a.out++Program.prepWord B1 B2 c C.wit ∧ Cst b ∧
        b.wq ≤ 5*(c.n+1)^5) := by
  let x := Builder.callInput c
  let L := (callWord c).length
  have hn : c.n ≤ L := n_le_callWord B1 B2 c
    (Program.admitted_of_admitted4 hadm) (Cells.admitted4_nonzero_topWeight hadm hW)
  have hvx : ValidInput x := Cells.callInput_valid c hadm hW
  have hb : 1 ≤ c.radius*(c.n:ℚ)^B1 := hadm.2.2.2.2.2.2.2.2.2.1
  have hbits := call_bounds c
  have hnumpos : 0<c.radius.num := Rat.num_pos.mpr (by exact hvx.2.2.2.2.1)
  have hbn : x.beta.num=(c.radius.num.natAbs:ℕ) := by
    change c.radius.num=(_ : ℤ)
    rw [Int.natCast_natAbs,abs_of_pos hnumpos]
  have hbd : x.beta.den=c.radius.den := rfl
  have htag : a.env vTAG=1 ↔ x.pair=true := by
    rw [hparse.tag]
    cases hkind : c.kind <;> simp [x,Builder.callInput,kindTag,hkind]
  have hW3 : 1 ≤ C.Wd := by
    have := Cells.ParameterArithmetic.preparationBitBase_bounds B1 L
    have hw : 100*Cells.ParameterArithmetic.preparationBitBase B1 L ≤ C.Wd := hwidth
    omega
  cases hp : Cells.prepare x with
  | none =>
    change Cells.prepare (Builder.callInput c)=none at hp
    unfold canonicalExit
    refine Hx.hs (Hs.then (canonicalPreparation_none_at_width C a hc x hvx
      B1 L c.radius.num.natAbs c.radius.den c.first.topWeight c.second.topWeight
      hbn hbd hparse.n hparse.c1.tw hparse.c2.tw hcount hparse.num hparse.den
      hparse.c1.g hparse.c2.g hparse.b0 htag ha hn hb hbits.2.2.2.1.le
      hbits.2.2.2.2.1.le hbits.2.1.le hbits.2.2.1.le hwidth hp)
      (fun b ⟨hba,_,hbwq,hbout,hbc⟩ n1 hn1 => ?_))
    refine Hs.last (Hs.iteF (show vADM≠v1 by decide)
      (by simp [Cnd.eval,hba,hbc.one]) (defaultPreparationOutput_spec C b hbc)) ?_
    rintro d ⟨hdout,_,hdwq,hdc,_⟩ n2 hn2
    refine ⟨⟨?_,hdc,?_⟩,?_⟩
    · rw [hdout,hbout,prepWord_of_prepare_none c C.wit hadm hW hp]
      rfl
    · rw [hdwq,hbwq,hwq]
      exact Nat.zero_le _
    · simp only [canonicalExitCost,hp]
      change n1+n2+1 ≤ canonicalPreparationBudget x c.radius.num.natAbs c.radius.den+0+200
      have hdlen : defaultPreparationWord.length ≤ 25 := by
        simpa only [defaultPreparationWord,List.length_cons] using
          Nat.add_le_add_right Cells.soundDefault_outputWord_length 1
      have hdef : 2*defaultPreparationWord.length+3 ≤ 200 := by omega
      omega
  | some p =>
    change Cells.prepare (Builder.callInput c)=some p at hp
    have hs := Cells.prepare_spec x p hp
    let selected : Program.Selected c := ⟨p,hp⟩
    have hd : Program.dispatch B1 B2 c=some selected := by
      unfold Program.dispatch
      rw [if_pos (show Transfer.Admitted4 B1 B2 c ∧ Transfer.callWires c≠0 from ⟨hadm,hW⟩)]
      change (match h : Cells.prepare (Builder.callInput c) with
        | some q => some (⟨q,h⟩ : Program.Selected c)
        | none => none)=some selected
      split
      · rename_i q hq
        have he : q=p := Option.some.inj (hq.symm.trans hp)
        subst q
        rfl
      · rename_i hnone
        rw [hp] at hnone
        cases hnone
    unfold canonicalExit
    refine Hx.hs (Hs.then (Hs.addValid hW3 hv
      (canonicalPreparation_selected_at_width C a hc x p hs
        B1 L c.radius.num.natAbs c.radius.den c.first.topWeight c.second.topWeight
        hbn hbd hparse.n hparse.c1.tw hparse.c2.tw hcount hparse.num hparse.den
        hparse.c1.g hparse.c2.g hparse.b0 htag ha hn hb hbits.2.2.2.1.le
        hbits.2.2.2.2.1.le hbits.2.1.le hbits.2.2.1.le hwidth))
      (fun b ⟨⟨hm,hba,hr,hN,hND,hD,hDb,hcp,hwqb,hbout,hbc,hfr⟩,hvb⟩ n1 hn1 => ?_))
    have hpb : ParseOut c b := ParseOut.congr hparse (fun r h17 h56 =>
      hfr r (by omega) (selectedPreparationT_preserves_call r h17 h56))
    refine Hs.last (Hs.iteT (show vADM≠v1 by decide) (by simp [Cnd.eval,hba,hbc.one])
      (successfulOutput_from_memory C b hbc hvb c p hs B1 L hn le_rfl hb hwidth
        hm hpb hcw (hwqb.trans hwq) hr hN hND hD hDb)) ?_
    rintro d ⟨hdout,hdwq,_,hdc⟩ n2 hn2
    refine ⟨⟨?_,hdc,?_⟩,?_⟩
    · rw [hdout,hbout,prepWord_of_dispatch c C.wit selected hd]
    · rw [hdwq]
      exact (Nat.min_le_left _ _).trans (witnessReadLength_preparation_bound c p hs)
    · simp only [canonicalExitCost,hp]
      rw [canonicalPreparationBudget_of_some x _ _ p hp]
      omega

end NearQuarticWires.StagePrep
