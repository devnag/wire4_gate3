import Proof.Quartic.StagePrint.FinalPrintTarget
import Proof.Quartic.StagePrint.GreedyHeaderCost
import Proof.Quartic.StageRecovery.NativeRecovery

/-!
# Actual native-header and recovered-table endpoints of the final printer

Paper: `lem:print`, `lem:residue` and `prop:time`,
paper/paper.tex.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrintFinal

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Interfaces
open StagePrint

attribute [local irreducible] StageNativeHeader.nativeHeaderPrinter StageGreedyNativeData.nativeSupplier
  StageRecovery.nativeRecoveryWordFunction

/-- `lem:print`, paper/paper.tex: the
original request determines its actual complete native table and
recovery metadata, including all uncertified original columns. -/
noncomputable def native {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    StageRecovery.NativeRequest := ((StageGreedyNativeData.nativeSupplier B1 B2).val r).native

/-- `lem:print`, paper/paper.tex: the
actual header source is the original five-field collector stream,
with no additional table, count or common-generator input. -/
noncomputable def headerRequest {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    Downstream.NativeHeaderRequest := ((StageGreedyNativeData.nativeSupplier B1 B2).val r).headerRequest

/-- `prop:time`, paper/paper.tex: the
header budget is the exact declared budget of the actual cold header
machine on this original request's complete cut stream. -/
noncomputable def headerBudget {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : ℕ :=
  10^30*((headerRequest r).parameters.n+(native r).table.matrix.p+2)^20*
    ((headerRequest r).stream.length+(native r).table.count+1)

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual native-header program
consumes the literal collector output and constructs the actual
framed native-table input on every original witness. -/
noncomputable def headerWordFunction (B1 B2 : ℕ) :
    WordFunction (Greedy.PrintRequest B1 B2) GreedyCollector.word
      (fun r=>frame (native r).table.word) headerBudget where
  program:=StageNativeHeader.nativeHeaderPrinter.program
  realizes r:=by
    obtain ⟨receipt,hr,ho⟩:=StageNativeHeader.nativeHeaderPrinter.realizes (headerRequest r)
    have hw : (headerRequest r).word=GreedyCollector.word r:=StageGreedyNativeData.header_word_eq r
    refine ⟨receipt,?_,?_⟩
    · rw [←hw]
      exact hr
    · exact ho


/-- `lem:print`, paper/paper.tex: the
one retained record around the actual generated table is exactly
the existing recovery machine's literal input record. -/
theorem native_word_eq {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    NativeMiddle.word (r.prime^r.child.selected.1.e) (native r).table.word r.child.cellCall.ncol=
      (native r).word := by
  unfold StageRecovery.NativeRequest.word
  have hm:=((StageGreedyNativeData.nativeSupplier B1 B2).val r).modulus_eq
  have hc:=((StageGreedyNativeData.nativeSupplier B1 B2).val r).targetCount_eq
  change (native r).modulus=r.prime^r.child.selected.1.e at hm
  change (native r).targetCount=r.child.cellCall.ncol at hc
  rw [hm,hc]
  rfl

/-- `lem:print` and `lem:residue`, paper/paper.tex: the actual cold native recovery
machine prints the exact RAW canonical table required by the original
Greedy subroutine, with the existing published counting input only. -/
noncomputable def recoveryWordFunction
    (h : Bindings.Williams14.Williams14_Corollary4_4) (B1 B2 : ℕ) :
    WordFunction (Greedy.PrintRequest B1 B2) (fun r=>(native r).word)
      (fun r=>listWord intWord (Greedy.printTable r)) (fun r=>(native r).recoveryBudget h) where
  program:=(StageRecovery.nativeRecoveryWordFunction h).program
  realizes r:=by
    have hr:=(StageRecovery.nativeRecoveryWordFunction h).realizes (native r)
    have ho:=((StageGreedyNativeData.nativeSupplier B1 B2).val r).output_eq
    change (native r).output=listWord intWord (Greedy.printTable r) at ho
    simpa only [ho] using hr

/-- `prop:time`, paper/paper.tex: the
exact actual header budget has a selected original-column bound. -/
theorem headerBudget_selected
    (h : Bindings.Williams14.Williams14_Corollary4_4) (B1 B2 : ℕ) :
    ∃K e : ℕ,∀r : Greedy.PrintRequest B1 B2,
      headerBudget r≤K*r.child.cellCall.ncol*(r.child.call.n+1)^e :=
  GreedyCost.native_header_selected h B1 B2

/-- `prop:time`, paper/paper.tex: the
exact actual recovery budget has a selected original-column bound. -/
theorem recoveryBudget_selected
    (h : Bindings.Williams14.Williams14_Corollary4_4) (B1 B2 : ℕ) :
    ∃K e : ℕ,∀r : Greedy.PrintRequest B1 B2,
      (native r).recoveryBudget h≤K*r.child.cellCall.ncol*(r.child.call.n+1)^e := by
  obtain ⟨K,e,hK⟩:=GreedyCost.native_recovery_selected h B1 B2
  refine ⟨K,e,fun r=>?_⟩
  have hn : native r=StageGreedyNativeData.nativeRequest r := by
    unfold native StageGreedyNativeData.nativeSupplier StageGreedyNativeData.nativeData
    rfl
  rw [hn]
  exact hK r

end NearQuarticWires.StagePrintFinal
