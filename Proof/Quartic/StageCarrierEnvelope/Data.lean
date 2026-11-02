import Proof.Quartic.StagePrint.CarrierEnvelopeTarget
import Proof.Quartic.StagePrint.CarrierSource
import Proof.Quartic.StagePrintContext.Capacity
import Proof.Quartic.StageLiftSourceCost.Reserve

set_option autoImplicit false

namespace NearQuarticWires.StageCarrierEnvelope

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open StagePrint

/-- `lem:print`, paper/paper.tex: the only
small source prefix is the actual original successful preparation. -/
def prepared {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : StageCertTests.PreparedScheduleRequest B1 B2 :=
  ⟨r.child.call,r.child.witness,r.child.selected,r.child.dispatched⟩

/-- `lem:print`, paper/paper.tex: both source
descriptions are the same literal finite preparation bytes. -/
theorem prepared_word {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    (prepared r).word=StageLift.preparedWordOf r := by
  change Program.prepWord B1 B2 r.child.call r.child.witness=_
  rw [StageMain.Compact.prepWord_eq_compact r.child.dispatched]
  rfl

/-- `lem:print`, paper/paper.tex: the original
sampler has an actual first compiled entry, including zero-weight walks. -/
noncomputable def firstIndex {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    Fin (r.child.cellCall.seed.N^8) := ⟨0,StageLiftSourceCost.walkCount_pos r⟩

/-- `lem:print`, paper/paper.tex: every raw
compiled entry is retained in its unchanged original order. -/
noncomputable def entries {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : List (List Bool) :=
  List.ofFn (TermsCarrier.entryWord r)

/-- `lem:print`, paper/paper.tex: the original
carrier exposes the first real entry after its one actual preparation
and binary walk count, with an arbitrary untouched remaining suffix. -/
theorem carrier_prefix {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    TermsCarrier.word r=
      natWord (StageLift.preparedWordOf r).length++StageLift.preparedWordOf r++
      natWord (r.child.cellCall.seed.N^8)++TermsCarrier.entryWord r (firstIndex r)++
      (entries r).tail.flatten := by
  have hne : entries r≠[] := by
    intro h
    have hh:=congrArg List.length h
    simp only [entries,List.length_ofFn,List.length_nil] at hh
    have hp:=StageLiftSourceCost.walkCount_pos r
    omega
  have hfirst : (entries r).head hne=TermsCarrier.entryWord r (firstIndex r) := by
    unfold entries
    rw [List.head_ofFn]
    rfl
  have hs:=List.cons_head_tail hne
  rw [hfirst] at hs
  unfold TermsCarrier.word
  change _=natWord (StageLift.preparedWordOf r).length++StageLift.preparedWordOf r++
    natWord (r.child.cellCall.seed.N^8)++TermsCarrier.entryWord r (firstIndex r)++_
  change _++(entries r).flatten=_
  rw [←hs,List.flatten_cons]
  simp only [List.append_assoc,List.tail_cons]

/-- `imp:partition`, paper/paper.tex: the exact
canonical original column count includes every free center bit. -/
theorem ncol_eq {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    r.child.cellCall.ncol=2^(r.child.call.n-r.child.selected.1.k) := rfl

end NearQuarticWires.StageCarrierEnvelope
