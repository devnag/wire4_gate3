import Proof.Quartic.StagePrintTuple.MonomialReady
import Proof.Wire_3_5.UnionMachineRoundDiv

set_option autoImplicit false

namespace NearQuarticWires.StageTuple

open NearCubicWires.WireExponent3_5.FinalPass.Tm

/-- `lem:print`, paper/paper.tex: the literal
source/copy/rewind monomial program has no result-cell write, so its
actual execution preserves that cell as well as all exterior sources. -/
theorem monomialReadyIn_cell {ns nr cap steps : ℕ}
    (P : Fin 3↪Fin (ns+1)) (R : Fin 11↪Fin nr)
    {σ τ : WState ns nr} (h : WExec cap (monomialReadyIn P R) σ τ steps) :
    τ.cell=σ.cell :=
  NearCubicWires.WireExponent3_5.UnionMachine.Round.cellFree_cell cap (by rfl) h

end NearQuarticWires.StageTuple
