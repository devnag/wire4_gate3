import Proof.Quartic.StageLift.ResidueCacheContract

/-!
# The exact residue source syntax

`lem:residue` and `imp:amp`, paper/paper.tex: the generated syntax uses the original circuit-major
score and digit factors, their literal Fermat product, and the full
integer Beigel–Tarui amplifier before coefficient normalization.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftTokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats StageLift

variable {B1 B2 : ℕ}

noncomputable def requestForm (r : Greedy.PrintRequest B1 B2) :=
  callResidueForm r.child.call (Cells.prepare_spec _ r.child.selected.1 r.child.selected.2)
    r.child.witness r.pattern

noncomputable def requestTarget (r : Greedy.PrintRequest B1 B2) :=
  callResidueTarget r.child.call r.child.selected.1 r.prime
    (fun j i=>r.digits j i % (r.prime^r.child.selected.1.e : ℤ))
    (fun j=>r.residues j % (r.prime^r.child.selected.1.e : ℤ))

noncomputable def requestFactor (r : Greedy.PrintRequest B1 B2)
    (i : Fin 2 × Option (Fin (r.child.selected.1.J-1+1))) :=
  Formula.sub (.const 1) (.pow (.sub (requestForm r i) (.const (requestTarget r i))) (r.prime-1))

noncomputable def requestFermat (r : Greedy.PrintRequest B1 B2) :=
  indexedFermatFormula r.prime (requestForm r) (requestTarget r)

theorem requestFactor_tokens (r : Greedy.PrintRequest B1 B2)
    (i : Fin 2 × Option (Fin (r.child.selected.1.J-1+1))) :
    (toks (requestFactor r i)).flatMap tokWord=
      tokWord (.const 1)++(toks (requestForm r i)).flatMap tokWord++tokWord (.const (requestTarget r i))++
        tokWord .sub++tokWord (.pow (r.prime-1))++tokWord .sub := by
  simp only [requestFactor,toks,List.flatMap_append,List.flatMap_singleton,List.append_assoc]

theorem residueBodyFormula_eq (r : Greedy.PrintRequest B1 B2) :
    residueBodyFormula r=Formula.amp r.child.selected.1.e (requestFermat r) := rfl

end NearQuarticWires.StageLiftTokens
