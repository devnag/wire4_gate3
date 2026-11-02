import Proof.Quartic.StagePrint.ChildTuples
import Proof.Quartic.StagePrint.StackPrinter
import Proof.Quartic.StagePrintTuple.CoefficientMachine
import Proof.Quartic.StagePrintTuple.SupportIndexMachine

set_option autoImplicit false

namespace NearQuarticWires.StageTuple

open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Interfaces

/-- `prop:time`, paper/paper.tex: the actual
Cartesian word-function clock has at most quadratic factors in its
real child and suffix-tuple counts, with only structural polynomial
factors in fixed field width and row strides. -/
abbrev ChildTupleCostBound : Prop :=
  ∃ C E : ℕ, 1 ≤ C ∧ 1 ≤ E ∧ ∀ r : StagePrint.ChildTupleRequest,
    2*r.budget+2 ≤ C*(r.L+r.N+r.M+1)^E*
      (r.children.length+1)^2*(r.tuples.length+1)^2

/-- `prop:time`, paper/paper.tex: the actual
signed Stack word-function clock has at most a quadratic factor in its
real tuple count, independently of coefficient magnitude beyond the
request's actual fixed signed field width. -/
abbrev StackCostBound : Prop :=
  ∃ C E : ℕ, 1 ≤ C ∧ 1 ≤ E ∧ ∀ r : StagePrint.StackRequest,
    2*r.budget+2 ≤ C*(r.W+r.s+r.m+1)^E*(r.tuples.length+1)^2

/-- `prop:time`, paper/paper.tex: actual signed
coefficient conversion is charged only against its genuine small
width/coefficient packet, independently of the complete Terms source. -/
abbrev CoefficientCostBound : Prop :=
  ∃ C E : ℕ, 1 ≤ C ∧ 1 ≤ E ∧ ∀ r : CoefficientRequest,
    r.budget ≤ C*(r.width+(intWord r.coefficient).length+1)^E

/-- `prop:time`, paper/paper.tex: actual support
selection is charged only against its one finite support cache and
computed finite index, independently of the complete Terms source. -/
abbrev SupportIndexCostBound : Prop :=
  ∃ C E : ℕ, 1 ≤ C ∧ 1 ≤ E ∧ ∀ r : SupportIndexRequest,
    r.budget ≤ C*(r.support.length+(listWord natWord r.support).length+1)^E

end NearQuarticWires.StageTuple
