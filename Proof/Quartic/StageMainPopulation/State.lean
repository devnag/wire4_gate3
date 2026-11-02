import Proof.Quartic.StageMainPopulation.SourceWords

set_option autoImplicit false

namespace NearQuarticWires.StageMainPopulation

open NearCubicWires
open NearCubicGates.Close.Dispatch
open StageMainMask StageCert

structure Retained (a : DS VV) (r : PopulationRequest) : Prop where
  corners : ∀ l, a.env (cornerPoint l) = r.corners l
  witnessBase : a.env sourceWitnessBase = (witnessPrefix r).length
  first : a.env firstStart = pos1 r.call

/-- `def:mask` and witness (W2), paper/paper.tex: both source scans retain the actual point codes and
witness address, while their own indices and total advance physically. -/
theorem Retained.frame {a b : DS VV} {r : PopulationRequest} {T : List (Fin VV)}
    (h : Retained a r) (hf : FrS a b T)
    (hp : ∀ l, cornerPoint l ∉ T) (hw : sourceWitnessBase ∉ T) (hs : firstStart ∉ T) :
    Retained b r :=
  ⟨fun l => (hf _ (by dsimp [cornerPoint]; have hl := l.isLt; omega) (hp l)).trans (h.corners l),
    (hf _ (by decide) hw).trans h.witnessBase, (hf _ (by decide) hs).trans h.first⟩

def firstValue (r : PopulationRequest) : ℕ :=
  populationPrefix r.call.first.gates r.corners r.witness r.offset r.call.first.gates.length

/-- `sec:cells` and `def:mask`, paper/paper.tex: the first bank's exact total admits the unconditional
two-per-occurrence bound, including arbitrary packed point codes. -/
theorem firstValue_le (r : PopulationRequest) : firstValue r ≤ 2 * r.call.first.gates.length :=
  populationPrefix_le _ _ _ _ _

end NearQuarticWires.StageMainPopulation
