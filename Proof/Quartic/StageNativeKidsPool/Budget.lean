import Proof.Quartic.StageNativeKidsPool.Families
import Proof.Quartic.StageNativeKidsPool.Loop
import Proof.Quartic.StageNativeKidsPool.CounterCall
import Proof.Quartic.StageNativeKidsPool.InitializationCost

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKidsPool
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Tabulator
open StageNativeKids StageNativeKidsPrice StageTuple StagePrint

/-- `lem:print`, paper/paper.tex: one
actual bank case determines the complete original-order row-call family
without introducing a row list, child choice or count input. -/
def actualFamily (a : SourceCase) : Family (OriginalPipelineRequest a.second) OriginalPipelineRequest.word where
  count:=(exactChildren (callAtoms a.request.header.call
    (a.request.toRowContext.originalIndex a.request.atom))).length
  source:=a.source.source
  header:=a.request.toRowContext.rowHeader a.request.atom
  request:=rowRequest a
  word_eq:=row_input a

/-- `lem:print`, paper/paper.tex: the
raw complete pool answer starts with the physically computed count and
copied target-width codecs and ends with one actual delimiter. -/
def actualAnswer (a : SourceCase) : List Bool:=
  natWord (actualFamily a).count++natWord a.request.outputWidth++
    suffix ((actualFamily a).bytes pipelineRecords) 0 (actualFamily a).count++[false]

/-- `prop:time`, paper/paper.tex: the
complete source clock includes actual fixed loading, one original
counter call, small-count initialization, every real row call and bank
reset, final raw delimiter and measured final frame construction. -/
noncomputable def actualPoolSteps (a : SourceCase) : ℕ:=
  1000*(Top.loadCost (frame (actualFamily a).source) (frame (actualFamily a).header)
    (natWord a.request.outputWidth) [] [] [] [] [] [] [] []+
    counterCopyCost (actualFamily a).source+indexedOriginalCountBudget a.source+
    initializeCost (actualFamily a).count a.request.outputWidth+
    (actualFamily a).count*((actualFamily a).stepBudget OriginalPipelineRequest.budget+10)+
    (actualAnswer a).length+1)

/-- `prop:time`, paper/paper.tex: the
actual ordinary pool clock adds the complete final head-return wrapper
to this same physical source program, without a second resource model. -/
noncomputable def actualPoolBudget (a : SourceCase) : ℕ:=2*actualPoolSteps a+2

/-- `prop:time`, paper/paper.tex: the
first actual-bank pool uses the same complete concrete compiled clock. -/
noncomputable def firstPoolBudget (q : FirstBankRequest) : ℕ:=actualPoolBudget ⟨q.val,false,q.property⟩

/-- `prop:time`, paper/paper.tex: the
second actual-bank pool uses the identical complete clock after only
its actual original-bank occurrence offset has changed. -/
noncomputable def secondPoolBudget (q : SecondBankRequest) : ℕ:=actualPoolBudget ⟨q.val,true,q.property⟩

/-- `prop:time`, paper/paper.tex: both
complete actual pool clocks have a uniform polynomial in original
source size, original arity and the unchanged sharp original child cap;
only the encoded target-width length is charged before resizing. -/
def ActualPoolPrice : Prop:=
  ∃K e : ℕ,∀a : SourceCase,actualPoolBudget a≤K*a.request.originalSourceScale^e

end NearQuarticWires.StageNativeKidsPool
