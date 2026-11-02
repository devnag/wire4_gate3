import Proof.Quartic.StageGreedyEntry.Format
import Proof.Quartic.StageGreedyCollector.EntryBounds

/-!
# The selected clock of the shared formatter on one entry

Paper: `lem:print`, `sec:params` and `prop:time`, paper/paper.tex.

The literal entry word has a small original context, four binary scalars and one framed Terms list.
Its distinct supports have degree at most `D` over `V = 17·|gates|` atoms, so the weighted census at
child count one bounds the number of records by `(1+V)^(2D) ≤ Uocc^(2D)`; each record has polynomial
height. The formatter is linear in this word, which gives `formatter_bound`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyEntry

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats
open StagePrint StageGreedyEntryBounds

/-- `sec:params`, paper/paper.tex: the occurrence factor
dominates one more than the original atom count. -/
theorem atoms_le_Uocc {B1 B2 : ℕ} (r : GreedyEntry.Request B1 B2) :
    1+17*(Builder.allGates r.source.child.call).length ≤ r.source.child.selected.1.Uocc := by
  have hs:=Cells.prepare_spec _ r.source.child.selected.1 r.source.child.selected.2
  have hg : (Builder.allGates r.source.child.call).length≤2*r.source.child.call.n^4 := by
    have hh:=hs.input_valid.2.2.1.trans hs.input_valid.2.2.2.1
    simpa only [Builder.callInput,Builder.allGates,List.length_append] using hh
  have hn:=hs.n_pos
  have hc : 1≤r.source.child.selected.1.childCap := by
    rw [hs.childCap_eq]
    unfold Cells.childCap
    exact Nat.mul_pos hn (by omega)
  rw [hs.Uocc_eq,hs.NatAtoms_eq,hs.m_eq]
  change 1+17*(Builder.allGates r.source.child.call).length≤
    1+17*(2*r.source.child.call.n^4)*r.source.child.selected.1.childCap
  have h1 : 17*(Builder.allGates r.source.child.call).length≤17*(2*r.source.child.call.n^4) :=
    Nat.mul_le_mul_left _ hg
  have h2 : 17*(2*r.source.child.call.n^4)≤17*(2*r.source.child.call.n^4)*r.source.child.selected.1.childCap :=
    Nat.le_mul_of_pos_right _ hc
  omega

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual Terms list has at most `Uocc^(2D)` records. -/
theorem terms_length_le {B1 B2 : ℕ} (r : GreedyEntry.Request B1 B2) :
    r.terms.length ≤ r.source.child.selected.1.Uocc^(2*r.degree) := by
  have h:=r.termRequest.weighted_census 1
  have hl : (r.termRequest.terms.map (fun t=>1^(2*t.1.card))).sum=r.terms.length := by
    simp only [one_pow]
    change (r.terms.map (fun _=>1)).sum=r.terms.length
    simp
  rw [hl,Nat.mul_one] at h
  exact h.trans (Nat.pow_le_pow_left (atoms_le_Uocc r) _)

/-- `lem:print`, paper/paper.tex: the serialized Terms
list is at most its record count times the polynomial record height. -/
theorem termsWord_length_le {B1 B2 : ℕ} (r : GreedyEntry.Request B1 B2) :
    (termsWord r.terms).length ≤
      r.terms.length*(recordHeight (17*(Builder.allGates r.source.child.call).length) r.coefficientBits+2)+3 := by
  have hhead:=NearCubicGates.Close.Expand.Layout.natWord_len_le r.terms.length r.terms.length
    Nat.lt_two_pow_self
  have hsum:=List.sum_le_card_nsmul (r.terms.map fun t=>(monoWord t).length)
    (recordHeight (17*(Builder.allGates r.source.child.call).length) r.coefficientBits) (by
      intro value hv
      obtain ⟨t,ht,rfl⟩:=List.mem_map.mp hv
      exact monoWord_length _ _ t (r.coefficient_bits t ht))
  simp only [List.length_map,smul_eq_mul] at hsum
  simp only [termsWord,listWord,List.length_append,List.length_flatMap]
  nlinarith only [hhead,hsum]

/-- `lem:print` and `prop:time`, paper/paper.tex: the literal entry word is polynomial in the original source
envelope times the selected census `Uocc^(2D)`. -/
theorem word_length_le {B1 B2 : ℕ} (r : GreedyEntry.Request B1 B2) :
    (EntryFormat.ofGreedy r).word.length+1 ≤
      10^27*(entryEnvelope r+1)^8*(r.source.child.selected.1.Uocc^(2*r.degree)+1) := by
  obtain ⟨h2,hn,hg,hd,hq,hi⟩:=entry_headers r
  have hc:=context_length r
  have ht:=termsWord_length_le r
  have hT:=terms_length_le r
  obtain ⟨E,hE⟩ : ∃E,E=entryEnvelope r := ⟨_,rfl⟩
  obtain ⟨U,hU⟩ : ∃U,U=r.source.child.selected.1.Uocc^(2*r.degree) := ⟨_,rfl⟩
  obtain ⟨T,hTd⟩ : ∃T,T=r.terms.length := ⟨_,rfl⟩
  obtain ⟨R,hR⟩ : ∃R,R=recordHeight (17*(Builder.allGates r.source.child.call).length) r.coefficientBits :=
    ⟨_,rfl⟩
  obtain ⟨W,hW⟩ : ∃W,W=(termsWord r.terms).length := ⟨_,rfl⟩
  rw [←hR,←hW] at ht
  rw [←hE] at h2 hn hg hd hq hi hc ⊢
  rw [←hU] at hT ⊢
  rw [←hTd] at hT ht
  have hQ2 : r.coefficientBits≤(E+1)^2 := hq
  have hVE : 17*(Builder.allGates r.source.child.call).length≤17*E := by omega
  have hw : (EntryFormat.ofGreedy r).word.length=
      (natWord r.source.child.call.n).length+(EntryFormat.ofGreedy r).contextWord.length+
        (natWord r.index.val).length+(natWord r.degree).length+(natWord r.modulus).length+
        (2*(termsWord r.terms).length+1) := by
    change (natWord r.source.child.call.n++(EntryFormat.ofGreedy r).contextWord++natWord r.index.val++
      natWord r.degree++natWord r.modulus++frame (termsWord r.terms)).length=_
    simp only [List.length_append,frame_length]
  have w1:=NearCubicWires.WireExponent3_5.PrimAsm.CallSize.natWord_len_le
    (NearCubicGates.Close.Dispatch.natBitLength_le_succ r.source.child.call.n)
  have w2:=NearCubicWires.WireExponent3_5.PrimAsm.CallSize.natWord_len_le hi
  have w3:=NearCubicWires.WireExponent3_5.PrimAsm.CallSize.natWord_len_le
    (NearCubicGates.Close.Dispatch.natBitLength_le_succ r.degree)
  have w4:=NearCubicWires.WireExponent3_5.PrimAsm.CallSize.natWord_len_le hq
  have hS1 : 1≤E+1 := by omega
  have hSS : E+1≤(E+1)^2 := Nat.le_self_pow (by decide) _
  have hS28 : (E+1)^2≤(E+1)^8 := Nat.pow_le_pow_right hS1 (by decide)
  have hrh : R+2≤1000*(E+1)^2 := by
    rw [hR]
    unfold recordHeight
    obtain ⟨V,hV⟩ : ∃V,V=17*(Builder.allGates r.source.child.call).length := ⟨_,rfl⟩
    rw [←hV] at hVE ⊢
    have hVV : V*(2*V+3)≤(17*(E+1))*(34*(E+1)+3) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hsq : (E+1)*(E+1)=(E+1)^2 := by ring
    nlinarith only [hVV,hsq,hQ2,hSS,hVE]
  have hTR : T*(R+2)≤U*(1000*(E+1)^2) := Nat.mul_le_mul hT hrh
  have hUS : U*(1000*(E+1)^2)≤U*(1000*(E+1)^8) := Nat.mul_le_mul_left _ (by omega)
  have hfin : 10^27*(E+1)^8*(U+1)=10^27*(E+1)^8+1000*(10^24*(U*(E+1)^8)) := by ring
  rw [hw,hfin,←hW]
  nlinarith only [w1,w2,w3,w4,hc,ht,hTR,hUS,hSS,hS28,hn,hd]

/-- `lem:print` and `prop:time`, paper/paper.tex: the formatter's clock meets the selected per-entry bound. -/
theorem formatter_bound (B1 B2 : ℕ) : StageGreedyCollector.EntryBudgetBound (formatterBudget B1 B2) := by
  obtain ⟨K,e,hK⟩:=EntryFormat.allocatedBudget_linear
    (StageEntryAllocation.allocation (sizingC B1 B2) (sizingE B1 B2) true)
  obtain ⟨C,E,hC⟩:=entryEnvelope_polynomial B1 B2
  refine ⟨K*10^27*C^8,e+8*E,fun r=>?_⟩
  have h1:=hK (bounded r)
  have h2:=word_length_le r
  have h4 : (entryEnvelope r+1)^8≤C^8*(r.source.child.call.n+1)^(8*E) := by
    calc
      _≤(C*(r.source.child.call.n+1)^E)^8 := Nat.pow_le_pow_left (hC r) 8
      _=_ := by ring
  change formatterBudget B1 B2 r≤_
  unfold formatterBudget
  calc
    _≤K*((EntryFormat.ofGreedy r).word.length+1)*(r.source.child.call.n+1)^e := h1
    _≤K*(10^27*(entryEnvelope r+1)^8*(r.source.child.selected.1.Uocc^(2*r.degree)+1))*
        (r.source.child.call.n+1)^e := by gcongr
    _≤K*(10^27*(C^8*(r.source.child.call.n+1)^(8*E))*(r.source.child.selected.1.Uocc^(2*r.degree)+1))*
        (r.source.child.call.n+1)^e := by gcongr
    _=_ := by ring

end NearQuarticWires.StageGreedyEntry
