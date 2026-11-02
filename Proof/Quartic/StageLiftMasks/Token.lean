import Proof.Quartic.StageLiftMasks.State
import Proof.Quartic.StageLift.Literal

/-!
# Literal product tokens with retained original sources

`lem:print`, paper/paper.tex: the constant and
multiplication tokens in the eight-mask product use the literal
postfix codec and preserve all retained source records and metadata.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftMasks
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open StageLift StageCert.Tokens

theorem emitOperator_ready {B1 B2 width L B : ℕ} (input : List Bool)
    (r : Greedy.PrintRequest B1 B2) (index : Fin (r.child.cellCall.seed.N^8))
    (a : DS VV MM) (h : PrintMasksReady width input L B r index a) (token : Tok) :
    Hs (structuralSourceContext B1 B2 width input L B) (emitOperator token) a
      (2*(tokWord token).length+1) (fun b=>b.out=a.out++tokWord token ∧
        PrintMasksReady width input L B r index b ∧ MaskFrame a b) := by
  obtain ⟨b,n,he,hn,bo,bs,bc,bfr⟩:=emitOperator_spec
    (structuralSourceContext B1 B2 width input L B) token a h.residue.constants
  simp only [Prod.mk.injEq] at bs
  have hf : MaskFrame a b := ⟨bs.2.1,fun s _=>congrFun bs.2.2.1 s,bs.1,
    fun x hx=>bfr x ((show ∀x∈maskRegisters,x∉[vJ] by decide) x hx)⟩
  exact ⟨b,n,he,hn,bo,ready_of_frame h bc (ready_execution_valid h he) hf
    (bs.2.2.2.1.trans h.inputEmpty),hf⟩

end NearQuarticWires.StageLiftMasks
