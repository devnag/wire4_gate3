import Proof.Quartic.StagePrintTuple.TermStageCost
import Proof.Quartic.StageNativeKids.TermPrice

set_option autoImplicit false

namespace NearQuarticWires.StageTuple

/-- `prop:time`, paper/paper.tex: the actual
complete monomial clock is polynomial in original structural data and
the original child cap, times the square census of that actual support.
The native budget is the genuine fixed source printer's own budget. -/
abbrev TermStageCostBound : Prop :=
  ∃ C E : ℕ,1 ≤ C ∧ 1 ≤ E ∧ ∀ (r : TermCutRequest) (mc : ℕ),
    1 ≤ mc → (∀i,(r.toRowContext.nativeKids i).length ≤ mc) →
      ∀ (k : ℕ) (hk : k<r.terms.length),
        termStageCost StageNativeKids.NativeKidsRequest.budget r k hk ≤
          C*(r.censusMagnitude mc)^E*mc^(2*r.terms[k].1.card)

end NearQuarticWires.StageTuple
