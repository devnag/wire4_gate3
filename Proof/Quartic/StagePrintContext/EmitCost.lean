import Proof.Quartic.StagePrintContext.Framing

set_option autoImplicit false

namespace NearQuarticWires.StagePrintContext

open NearCubicWires
open NearCubicGates.Close.Cells

/-- `prop:time`, paper/paper.tex: a fixed list
of actual scalar fields has clock linear in the loaded binary width. -/
def fieldClock (count width : ℕ) : ℕ := count*(40*width+43)+1

/-- `prop:time`, paper/paper.tex: validity of
the actual loaded state bounds every serialized field's bit length. -/
theorem headerEmitCost_valid (C : Ctx) (fields : List (Fin VV)) (a : DS VV MM)
    (ha : Valid C a) (hW : 1≤C.Wd) :
    StagePrint.Header.headerEmitCost (fields.map a.env)≤fieldClock fields.length C.Wd := by
  have hsum:=List.sum_le_card_nsmul (fields.map fun field=>40*natBitLength (a.env field)+43)
    (40*C.Wd+43) (by
      intro value hv
      obtain ⟨field,_hfield,rfl⟩:=List.mem_map.mp hv
      have hh:=NearCubicGates.Close.Dispatch.natBitLength_le_of_lt (ha.env_lt field) hW
      omega)
  simpa only [StagePrint.Header.headerEmitCost,List.map_map,Function.comp_def,List.length_map,smul_eq_mul,
    fieldClock] using Nat.add_le_add_right hsum 1

end NearQuarticWires.StagePrintContext
