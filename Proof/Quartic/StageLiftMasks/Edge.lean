import Proof.Quartic.StageLiftMasks.Load
import Proof.Quartic.StageLiftMasks.Reload
import Proof.Quartic.StageLiftMasks.Emit

/-!
# One original edge mask from actual source bytes

`def:mask` and `lem:print`, paper/paper.tex: each edge first executes the structural query,
then reloads the original mask parameters and emits the complete
guarded-tuple formula. The call, reloads and enumeration are charged.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftMasks
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open StageLift StageCert.Tokens

def edgeProgram (edge : Fin 8) : St VV MM :=
  .seq (edgeStructural edge) (.seq loadMaskParameters (emitMask witnessStore edge))

noncomputable def edgeCost {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) (L B : ℕ) : ℕ :=
  originalMaskCost r+9*(preparedWordOf r).length+80*(sourceEnvelope r+1)+L+B+1000

theorem edgeProgram_run {B1 B2 width L B : ℕ} (input : List Bool)
    (r : Greedy.PrintRequest B1 B2) (index : Fin (r.child.cellCall.seed.N^8))
    (edge : Fin 8) (a : DS VV MM) (h : PrintMasksReady width input L B r index a) :
    Hs (structuralSourceContext B1 B2 width input L B) (edgeProgram edge) a (edgeCost r L B)
      (fun b=>b.out=a.out++(toks (edgeMaskFormula r index edge)).flatMap tokWord ∧
        PrintMasksReady width input L B r index b ∧ MaskFrame a b) := by
  unfold edgeProgram
  apply Hx.hs
  refine Hs.then (edgeStructural_run input r index edge a h)
    (fun b ⟨bo,br,bf,bflag⟩ n1 hn1=>?_)
  refine Hs.then (loadMaskParameters_ready input r index b br)
    (fun d ⟨doo,dr,df,dt,dx,dk,ds⟩ n2 hn2=>?_)
  refine Hs.last (emitOriginalMask_run input r index edge d dr dt dx dk (ds.trans bflag))
    (fun z ⟨zo,zr,zf⟩ n3 hn3=>?_)
  refine ⟨⟨by rw [zo,doo,bo],zr,bf.trans (df.trans zf)⟩,?_⟩
  unfold edgeLoadCost at hn1
  unfold edgeCost
  omega

end NearQuarticWires.StageLiftMasks
