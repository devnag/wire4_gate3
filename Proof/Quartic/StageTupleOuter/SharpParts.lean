import Proof.Quartic.StageTupleOuter.Cost
import Proof.Quartic.StageTupleOuter.SharpOutput
import Proof.Quartic.StagePrintTuple.TermsCount

/-!
# The parts of the sharp tuple ledger

Paper: `lem:print` and `prop:time`, paper/paper.tex.

Write `T = |termsWord r.terms|`, `X = (1+17G·mc)^(2D)` and `c = r.censusMagnitude mc`. The literal request
word and the prepared word contain the Terms bytes once and otherwise only small fields
(`word_length_le`, `preparedWord_length_le`); the loader is linear in the prepared word
(`preparedLoadCost_eq`); initialization decodes two small widths and the Terms count, whose square is in the
census (`kernelInitializeCost_le`); the counted loop pays the sum of the monomial clocks
(`countedSourceCost_le`).
-/

set_option autoImplicit false

namespace NearQuarticWires.StageTupleOuter

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats
open StageTuple

theorem natWord_len (v : ℕ) : (natWord v).length ≤ 2*v+3 :=
  NearCubicWires.WireExponent3_5.PrimAsm.CallSize.natWord_len_le_self v

/-- `lem:print`, paper/paper.tex: the request word holds the Terms bytes once. -/
theorem word_length_le (r : TermCutRequest) :
    r.word.length ≤ 4*r.setupStructuralMagnitude+2*(termsWord r.terms).length+30 := by
  have hW:=natWord_len r.stackWidth
  unfold TermCutRequest.word TermCutRequest.setupStructuralMagnitude
  simp only [Top.loadRec,List.length_append,frame_length,List.length_nil]
  omega

/-- `lem:print`, paper/paper.tex: the prepared word holds the Terms bytes once. -/
theorem preparedWord_length_le (r : TermCutRequest) :
    r.preparedWord.length ≤ 2*(termsWord r.terms).length+30*(r.setupStructuralMagnitude+r.rowDimension)+60 := by
  have h1:=natWord_len (r.stackWidth+1)
  have h2:=natWord_len (r.rowDimension+1)
  have h3:=NearCubicGates.Close.Dispatch.natBitLength_le_succ (r.stackWidth+1)
  have h4:=NearCubicGates.Close.Dispatch.natBitLength_le_succ (r.rowDimension+1)
  unfold TermCutRequest.preparedWord TermCutRequest.preparedFields TermCutRequest.setupStructuralMagnitude
  simp [Top.loadRec,frame_length,CoefficientRequest.output]
  omega

/-- `prop:time`, paper/paper.tex: the eleven-field loader is linear. -/
theorem preparedLoadCost_eq (r : TermCutRequest) : r.preparedLoadCost=6*r.preparedWord.length+27 := by
  unfold TermCutRequest.preparedLoadCost TermCutRequest.preparedWord
  simp only [Top.loadCost,Top.loadChainCost,Top.loadRec,List.length_append,frame_length]
  ring

theorem scalarReadCost_le (j : ℕ) : scalarReadCost j ≤ 1000*(j+1)^2 :=
  natural_count_readCost_le j

/-- `prop:time`, paper/paper.tex: initialization decodes two small widths and the Terms
count, whose square lies in the census. -/
theorem kernelInitializeCost_le (r : TermCutRequest) (mc : ℕ) (hmc : 1 ≤ mc) :
    kernelInitializeCost r ≤ 1000*(r.stackWidth+2)^2+1000*(r.rowDimension+2)^2+
      2000*(1+17*(Builder.allGates r.header.call).length*mc)^(2*r.degree)+2017 := by
  have h1 : scalarReadCost (r.stackWidth+1) ≤ 1000*(r.stackWidth+2)^2 := scalarReadCost_le _
  have h2 : scalarReadCost (r.rowDimension+1) ≤ 1000*(r.rowDimension+2)^2 := scalarReadCost_le _
  have h3:=scalarReadCost_le r.terms.length
  have h4:=r.termCount_sq_le mc hmc
  have h5 : (r.terms.length+1)^2 ≤ 2*r.terms.length^2+2 := by nlinarith
  unfold kernelInitializeCost
  generalize (1+17*(Builder.allGates r.header.call).length*mc)^(2*r.degree)=X at h4 ⊢
  generalize r.terms.length^2=Q at h4 h5
  generalize (r.terms.length+1)^2=Q1 at h3 h5
  omega

theorem sum_range_getD {α : Type} (g : α → ℕ) (d : α) :
    ∀ (l pre : List α),((List.range' pre.length l.length).map (fun k=>g ((pre++l).getD k d))).sum=(l.map g).sum
  | [],_=>by simp
  | a::l,pre=>by
    have ih:=sum_range_getD g d l (pre++[a])
    simp only [List.length_append,List.length_singleton,List.append_assoc,List.singleton_append] at ih
    simp only [List.length_cons,List.range'_succ,List.map_cons,List.sum_cons,ih]
    congr 1
    simp

/-- `prop:time`, paper/paper.tex: the counted loop pays the SUM of the actual monomial
clocks, each charging only its own support's child-choice square. -/
theorem countedSourceCost_le (cost : ℕ → ℕ) (r : TermCutRequest) (mc K : ℕ)
    (hcost : ∀ (k : ℕ) (hk : k<r.terms.length),cost k ≤ K*mc^(2*r.terms[k].1.card)) (hmc : 1 ≤ mc) :
    countedSourceCost cost 0 r.terms.length ≤
      K*(1+17*(Builder.allGates r.header.call).length*mc)^(2*r.degree)+
        4*(1+17*(Builder.allGates r.header.call).length*mc)^(2*r.degree)+1 := by
  rw [countedSourceCost_eq_sum]
  obtain ⟨d,_⟩ : ∃d : Finset (Fin (17*(Builder.allGates r.header.call).length))×ℤ,True := ⟨(∅,0),trivial⟩
  have hs : ((List.range' 0 r.terms.length).map cost).sum ≤
      ((List.range' 0 r.terms.length).map (fun k=>K*mc^(2*(r.terms.getD k d).1.card))).sum := by
    apply List.sum_le_sum
    intro k hk
    rw [List.mem_range'] at hk
    have hk' : k<r.terms.length := by omega
    have h:=hcost k hk'
    rwa [List.getD_eq_getElem _ _ hk']
  have he:=sum_range_getD (fun t : Finset (Fin (17*(Builder.allGates r.header.call).length))×ℤ=>
    mc^(2*t.1.card)) d r.terms []
  simp only [List.length_nil,List.nil_append] at he
  rw [List.sum_map_mul_left,he] at hs
  have hw:=r.weighted_census mc
  have hn : r.terms.length ≤ (1+17*(Builder.allGates r.header.call).length*mc)^(2*r.degree) := by
    have h4:=r.termCount_sq_le mc hmc
    have : r.terms.length ≤ r.terms.length^2 := by nlinarith
    omega
  have hK:=Nat.mul_le_mul_left K hw
  omega

end NearQuarticWires.StageTupleOuter
