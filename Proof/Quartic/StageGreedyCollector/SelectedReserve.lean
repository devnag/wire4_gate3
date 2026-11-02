import Proof.Quartic.StageGreedyCollector.StageActual

set_option autoImplicit false

namespace NearQuarticWires.StageGreedyCollector

open NearCubicWires
open StagePrint

/-- `lem:print` and `sec:params`, paper/paper.tex: the actual walk count times the sharp
squared per-walk census fits the original selected outer-column reserve. -/
theorem entry_squared_reserve {B1 B2 : ℕ} (r : GreedyEntry.Request B1 B2) :
    r.source.child.cellCall.seed.N^8*r.source.child.selected.1.Uocc^(2*r.degree)≤
      2^(r.source.child.call.n-r.source.child.selected.1.k) := by
  let p:=r.source.child.selected.1
  let free:=r.source.child.call.n-p.k
  have hs:=Cells.prepare_spec _ p r.source.child.selected.2
  have hp:=hs.printing_entries r.degree (entry_degree_le r)
  rw [hs.m_eq] at hp
  change 2^(4*p.k)*p.Uocc^r.degree≤2^(free/100) at hp
  have hn:=StageLiftSourceCost.walkCount_le r.source
  change r.source.child.cellCall.seed.N^8≤2^(4*p.k) at hn
  have hsquare:=Nat.mul_le_mul hp hp
  have heq : (2^(4*p.k)*p.Uocc^r.degree)*(2^(4*p.k)*p.Uocc^r.degree)=
      2^(8*p.k)*p.Uocc^(2*r.degree) := by
    rw [show 8*p.k=4*p.k+4*p.k by omega,pow_add,
      show 2*r.degree=r.degree+r.degree by omega,pow_add]
    ring
  rw [heq,←pow_add] at hsquare
  have hw : r.source.child.cellCall.seed.N^8≤2^(8*p.k) :=
    hn.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have he : free/100+free/100≤free := by
    have hd:=Nat.div_mul_le_self free 100
    omega
  exact (Nat.mul_le_mul_right _ hw).trans
    (hsquare.trans (Nat.pow_le_pow_right (by decide) he))

/-- `prop:time`, paper/paper.tex: the
empty-body overhead for every original walk fits the same selected
reserve along with its actual squared child census. -/
theorem entry_squared_reserve_add {B1 B2 : ℕ} (r : GreedyEntry.Request B1 B2) :
    r.source.child.cellCall.seed.N^8*(r.source.child.selected.1.Uocc^(2*r.degree)+1)≤
      2*2^(r.source.child.call.n-r.source.child.selected.1.k) := by
  have hs:=entry_squared_reserve r
  have hn:=StageLiftSourceCost.walkCount_le_columns r.source
  rw [Nat.mul_add,Nat.mul_one]
  omega

end NearQuarticWires.StageGreedyCollector
