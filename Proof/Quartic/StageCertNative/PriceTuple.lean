import Proof.Quartic.StageCertNative.PriceTupleStructure

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires
open NearCubicGates.Close.Interfaces.Formats

/-- `sec:params` and `lem:print`, paper/paper.tex: the actual original child cap and
actual original occurrence bank are both included in the unchanged
selected occurrence base. -/
theorem actual_child_base_le {B1 B2 : ℕ} (r : TermJob B1 B2) :
    1+17*(Builder.allGates r.moment.call).length*r.moment.selected.1.childCap≤
      r.moment.selected.1.Uocc := by
  have hs:=r.moment.rules
  have hg:=StageCertSourceBounds.actual_gate_count_le r.moment
  rw [hs.Uocc_eq,hs.NatAtoms_eq,hs.m_eq]
  change 1+17*(Builder.allGates r.moment.call).length*r.moment.selected.1.childCap≤
    1+17*(2*r.moment.call.n^4)*r.moment.selected.1.childCap
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hg)) 1

theorem price_actualChildCensus (B1 B2 : ℕ) :
    JobPrice (fun r : TermJob B1 B2=>
      (1+17*(Builder.allGates r.moment.call).length*r.moment.selected.1.childCap)^
        (2*(termRequest r.base r.index).degree)) 2 := by
  refine ⟨1,0,fun r=>?_⟩
  change (1+17*(Builder.allGates r.moment.call).length*r.moment.selected.1.childCap)^
    (2*(termRequest r.base r.index).degree)≤_
  have hd : (termRequest r.base r.index).degree=r.moment.packet.degree := rfl
  rw [hd]
  have hh:=Nat.pow_le_pow_left (actual_child_base_le r) (2*r.moment.packet.degree)
  change _≤r.moment.selected.1.Uocc^(2*r.moment.packet.degree) at hh
  simpa only [pow_zero,one_mul] using hh

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual additive sharp Tuple
ledger has occurrence exponent two at every actual CERT source term.
All child and structural bounds here follow from the original request;
none is an additional physical source or counted input. -/
theorem price_tuple_of_ledger
    {B1 B2 : ℕ} {tb : StageTuple.TermCutRequest→ℕ} (C E : ℕ)
    (hledger : ∀t : StageTuple.TermCutRequest,∀mc : ℕ,
      1 ≤ mc→(∀i,(t.toRowContext.nativeKids i).length ≤ mc)→
      tb t≤C*(t.censusMagnitude mc)^E*
        ((1+17*(Builder.allGates t.header.call).length*mc)^(2*t.degree)+
          (termsWord t.terms).length+1)) :
    JobPrice (fun r : TermJob B1 B2=>tb (termRequest r.base r.index)) 2 := by
  have hsize:=((price_actualChildCensus B1 B2).add
    ((price_termsWord B1 B2).raise (by decide : 1≤2))).add
    ((JobPrice.constant 1).raise (by decide : 0≤2))
  have hpoly:=(JobPrice.constant C).mul ((price_tupleCensusMagnitude B1 B2).pow E)
  have hpoly' : JobPrice (fun r : TermJob B1 B2=>
      C*((termRequest r.base r.index).censusMagnitude r.moment.selected.1.childCap)^E) 0 := by
    simpa only [zero_mul,zero_add] using hpoly
  have hh:=hpoly'.mul hsize
  refine hh.mono ?_
  intro r
  have hpos : 1≤r.moment.selected.1.childCap := by
    have hn:=r.moment.rules.n_pos
    change 0<r.moment.selected.1.childCap
    rw [r.moment.rules.childCap_eq]
    unfold Cells.childCap
    positivity
  have hkids : ∀i,((termRequest r.base r.index).toRowContext.nativeKids i).length≤
      r.moment.selected.1.childCap := by
    intro i
    rw [r.moment.rules.childCap_eq]
    exact r.moment.nativeContext.nativeKids_length_le i r.moment.rules.n_pos
  exact hledger (termRequest r.base r.index) r.moment.selected.1.childCap hpos hkids

end NearQuarticWires.StageCertNative
