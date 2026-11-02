import Proof.Quartic.StageCert.MomentTermSum
import Proof.Quartic.StagePrint.CallEquationTables

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.WireExponent3_5.Shared

/-- `sec:walks` and `lem:print`, paper/paper.tex: the physical low-first source ordinal enumerates
all original eight-vertex walks exactly once. -/
def MomentRequest.walkTermEquiv {B1 B2 : ℕ} (r : MomentRequest B1 B2)
    (hcount : momentTermCount r.selected.1.N r.test=r.selected.1.N^8) :
    Fin (momentTermCount r.selected.1.N r.test) ≃ Cycle.Walk r.rules.seedParameters.N 4 :=
  (finCongr (hcount.trans (congrArg (fun N : ℕ=>N^8) r.rules.seed_N.symm))).trans
    finFunctionFinEquiv.symm

/-- `sec:walks` and `lem:print`, paper/paper.tex: every arithmetic digit is the exact corresponding
vertex in the original finite-function walk enumeration. -/
theorem MomentRequest.walkTermEquiv_eq {B1 B2 : ℕ} (r : MomentRequest B1 B2)
    (hcount : momentTermCount r.selected.1.N r.test=r.selected.1.N^8)
    (i : Fin (momentTermCount r.selected.1.N r.test)) :
    (r.withIndex i).walk=r.walkTermEquiv hcount i := by
  funext l
  apply Fin.ext
  change i.val/r.selected.1.N^l.val%r.selected.1.N=
    i.val/r.rules.seedParameters.N^l.val%r.rules.seedParameters.N
  rw [r.rules.seed_N]

/-- `eq:testX` and `lem:print`, paper/paper.tex: population uses the two low-first digits as its
row and column and contains every original cell once. -/
def MomentRequest.cellTermEquiv {B1 B2 : ℕ} (r : MomentRequest B1 B2)
    (ht : r.test=.population) :
    Fin (momentTermCount r.selected.1.N r.test) ≃ Sampler.Cell r.rules.seedParameters.N :=
  (finCongr (by rw [ht,momentTermCount,←r.rules.seed_N,pow_two])).trans
    (finProdFinEquiv.symm.trans (Equiv.prodComm _ _))

/-- `eq:testX` and `lem:print`, paper/paper.tex: the population source's actual edge zero is
exactly the cell addressed by its two low-first arithmetic digits. -/
theorem MomentRequest.population_edge_eq {B1 B2 : ℕ} (r : MomentRequest B1 B2)
    (ht : r.test=.population) (i : Fin (momentTermCount r.selected.1.N r.test)) :
    Cycle.edge (by decide : 0<4) (r.withIndex i).walk 0=r.cellTermEquiv ht i := by
  have hN : 0<r.selected.1.N := lt_of_lt_of_le (by decide : 0<2)
    (Cells.ParameterRules.N_ge_two r.rules)
  have hi : i.val<r.selected.1.N*r.selected.1.N := by
    simpa only [ht,momentTermCount,pow_two] using i.isLt
  have hd : i.val/r.selected.1.N<r.selected.1.N := (Nat.div_lt_iff_lt_mul hN).mpr hi
  apply Prod.ext
  · apply Fin.ext
    change i.val/r.selected.1.N^0%r.selected.1.N=i.val%r.rules.seedParameters.N
    rw [pow_zero,Nat.div_one,r.rules.seed_N]
  · apply Fin.ext
    change i.val/r.selected.1.N^1%r.selected.1.N=i.val/r.rules.seedParameters.N
    rw [pow_one,Nat.mod_eq_of_lt hd,r.rules.seed_N]

end NearQuarticWires.StageCert.Tokens
