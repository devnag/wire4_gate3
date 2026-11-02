import Proof.Quartic.StageTupleTermPrice.Data

set_option autoImplicit false

namespace NearQuarticWires.StageTupleTermPrice

open StageTuple

/-- `prop:time`, paper/paper.tex: the
actual final signed Stack call, complete current-source formatting,
measured cache erasure and current-history advancement consume only
the square census of the actual original support. -/
abbrev FinishCostBound : Prop :=
  ∃C E : ℕ,1≤C ∧ 1≤E ∧ ∀j : Case,
    100000000*monomialFinishMagnitude j.request
      (j.request.progressMonomial j.index j.index_lt) j.term j.term_mem≤
        C*j.small^E*j.childCap^(2*j.card)

end NearQuarticWires.StageTupleTermPrice
