import Proof.Quartic.StagePrintTuple.TermStagePriceContract
import Proof.Quartic.StageTupleCensusBounds.Child
import Proof.Quartic.StageTupleCensusBounds.Stack
import Proof.Quartic.StageTupleCensusBounds.Coefficient
import Proof.Quartic.StageTupleCensusBounds.Support
import Proof.Quartic.StagePrintTuple.TermsCount

set_option autoImplicit false

namespace NearQuarticWires.StageTupleTermPrice

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats
open StageTuple

/-- `lem:print` and `prop:time`, paper/paper.tex: the cost analysis uses exactly an actual monomial,
its original child bound and the original small structural magnitude. -/
structure Case where
  request : TermCutRequest
  childCap : ℕ
  childCap_pos : 1≤ childCap
  children_le : ∀i,(request.toRowContext.nativeKids i).length≤ childCap
  index : ℕ
  index_lt : index< request.terms.length

def Case.small (j : Case) : ℕ:=j.request.censusMagnitude j.childCap

def Case.term (j : Case) : Finset (Fin (17*(Builder.allGates j.request.header.call).length))×ℤ :=
  j.request.terms[j.index]'j.index_lt

def Case.order (j : Case) :=j.term.1.sort (·≤·)

def Case.support (j : Case) : List ℕ:=j.order.map Fin.val

def Case.card (j : Case) : ℕ:=j.term.1.card

def Case.width (j : Case) : ℕ:=j.request.stackWidth+1

theorem Case.term_mem (j : Case) : j.term∈j.request.terms:=List.getElem_mem j.index_lt

theorem Case.order_length (j : Case) : j.order.length=j.card:=Finset.length_sort _

theorem Case.support_length (j : Case) : j.support.length=j.card := by
  simp only [Case.support,List.length_map,Case.order_length]

theorem Case.card_le_degree (j : Case) : j.card≤ j.request.degree := by
  apply j.request.terms_degree j.term.1
  exact List.mem_map.mpr ⟨j.term,j.term_mem,rfl⟩

/-- `prop:time`, paper/paper.tex: every
scalar and original source byte used in this local analysis occurs in
the frozen structural magnitude, independently of Terms/history bytes. -/
theorem Case.small_bounds (j : Case) :
    10≤ j.small ∧ j.request.header.call.n≤ j.small ∧ j.width≤ j.small ∧
    j.request.rowDimension+1≤ j.small ∧ j.request.degree≤ j.small ∧
    17*(Builder.allGates j.request.header.call).length≤ j.small ∧ j.childCap≤ j.small ∧
    (callWord j.request.header.call).length≤ j.small ∧
    ((StagePrint.Header.baseHeaderValues j.request.header).flatMap natWord).length≤ j.small ∧
    j.request.contextWord.length≤ j.small := by
  unfold Case.small Case.width TermCutRequest.censusMagnitude TermCutRequest.setupStructuralMagnitude
  omega

theorem Case.card_le_small (j : Case) : j.card≤ j.small :=
  j.card_le_degree.trans j.small_bounds.2.2.2.2.1

theorem Case.support_member (j : Case) (v : ℕ) (hv : v∈j.support) : v≤ j.small := by
  obtain ⟨i,_hi,rfl⟩:=List.mem_map.mp hv
  exact i.isLt.le.trans j.small_bounds.2.2.2.2.2.1

end NearQuarticWires.StageTupleTermPrice
