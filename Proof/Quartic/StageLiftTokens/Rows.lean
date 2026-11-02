import Proof.Quartic.StageLiftTokens.Factor
import Proof.Quartic.StageLiftTokens.SourceLoop

/-!
# Every original digit row

`lem:residue` and `lem:print`, paper/paper.tex: the selected J counter controls the physical digit
loop. The circuit ordinal and amplifier ordinal survive every row,
and every emitted factor appears in the original finite row order.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftTokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open StageLift StageCert.Tokens

variable {B1 B2 : ℕ}

def rowsProgram : St VV MM := forS requestedChainRow degreeChain digitFactor

def rowSourceCost (E J : ℕ) : ℕ := J*(factorSourceCost E+4)+4

theorem rowsProgram_run (C : Ctx) (r : Greedy.PrintRequest B1 B2) (a : DS VV MM) (E : ℕ)
    (h : SourceReady C r a E) (j : Fin 2) (hj : a.env targetCircuit=j.val) :
    Hs C rowsProgram a (rowSourceCost E r.child.selected.1.J) (fun b=>
      b.out=a.out++(List.ofFn fun row : Fin (r.child.selected.1.J-1+1)=>
        (toks (requestFactor r (j,some row))).flatMap tokWord).flatten ∧
      SourceReady C r b E ∧ SourceFrame a b ∧ b.env targetCircuit=j.val ∧
      b.env amplifierIndex=a.env amplifierIndex) := by
  have hJ : r.child.selected.1.J-1+1=r.child.selected.1.J := by
    have hp:=(Cells.prepare_spec _ r.child.selected.1 r.child.selected.2).J_pos
    omega
  have hN : r.child.selected.1.J-1+1<2^C.Wd := by
    have hh:=h.target_room
    omega
  have hh:=source_forFin C r a E requestedChainRow degreeChain (by decide) (by decide)
    (by decide) digitFactor (r.child.selected.1.J-1+1) (factorSourceCost E)
    (fun row=>(toks (requestFactor r (j,some row))).flatMap tokWord)
    hN h (h.chainCount.trans hJ.symm) (fun b=>b.env targetCircuit=j.val) hj
    (by intro b v _ hb; rw [DS.set_env_ne _ _ (by decide)]; exact hb) (by
      intro row b hb bj bi bm
      refine (digitFactor_run C r b E hb j row bj bi).mono le_rfl ?_
      rintro d ⟨doo,dr,df,dfr⟩
      exact ⟨doo,dr,df,(dfr _ (by decide)).trans bj,
        (dfr _ (by decide)).trans bi,(dfr _ (by decide)).trans bm⟩)
  obtain ⟨b,n,he,hn,bo,br,bf,bj,_bi,_bm⟩:=hh
  exact ⟨b,n,he,by simpa only [hJ,rowSourceCost] using hn,bo,br,bf,bj,
    avoidsRegister_spec he (by decide)⟩

end NearQuarticWires.StageLiftTokens
