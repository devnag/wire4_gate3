import Proof.Quartic.StagePrint.BaseHeaderEmit
import Proof.Quartic.StageCertTests.PrepScheduleMachine

set_option autoImplicit false

namespace NearQuarticWires.StagePrint.Context

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.Interfaces

/-- `lem:print`, paper/paper.tex: the original
successful preparation determines one actual affine-header source,
independently of every walk, prime and test index. -/
def header {B1 B2 : ℕ} (r : StageCertTests.PreparedScheduleRequest B1 B2) : Header.HeaderCall :=
  ⟨r.call,r.selected.1,Cells.prepare_spec _ r.selected.1 r.selected.2,r.witness⟩

/-- `lem:print`, paper/paper.tex:
the original finite occurrence counts and selected sampler radix
are retained before a per-walk ordinal is appended. -/
def countsWord {B1 B2 : ℕ} (r : StageCertTests.PreparedScheduleRequest B1 B2) : List Bool :=
  [r.call.first.gates.length,r.call.second.gates.length,r.selected.1.N].flatMap natWord

/-- `imp:partition` and `lem:print`, paper/paper.tex: only the four actual original star scalars are needed
by the physical canonical-column constructor. -/
def geometryWord {B1 B2 : ℕ} (r : StageCertTests.PreparedScheduleRequest B1 B2) : List Bool :=
  [r.call.n,r.selected.1.r,r.selected.1.b,r.selected.1.s].flatMap natWord

/-- `lem:print`, paper/paper.tex: one context
contains literal call and affine-header frames, occurrence counts,
radix and geometry. No child pool, Formula or decoded row is included. -/
def word {B1 B2 : ℕ} (r : StageCertTests.PreparedScheduleRequest B1 B2) : List Bool :=
  Top.loadRec (frame (callWord r.call))
    (frame ((Header.baseHeaderValues (header r)).flatMap natWord))
    (countsWord r) (geometryWord r) [] [] [] [] [] [] []

/-- `lem:print` and `prop:time`, paper/paper.tex: the common context must be produced by an actual
cold source program from the literal preparation bytes. -/
abbrev Producer (B1 B2 : ℕ) :=
  (budget : StageCertTests.PreparedScheduleRequest B1 B2→ℕ) ×
    WordFunction (StageCertTests.PreparedScheduleRequest B1 B2)
      StageCertTests.PreparedScheduleRequest.word (fun r=>frame (word r)) budget

#check header
#check word
#check Producer

end NearQuarticWires.StagePrint.Context
