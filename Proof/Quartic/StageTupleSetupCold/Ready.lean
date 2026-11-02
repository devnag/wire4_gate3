import Proof.Quartic.StageTupleSetupCold.Initial

set_option autoImplicit false

namespace NearQuarticWires.StageTupleSetupCold

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Interfaces
open StageTuple

/-- `lem:print`, paper/paper.tex: the
retained original fields, physically framed context and degree, fresh
output and four finite private rulers are available throughout the
four small helper calls. No prepared helper reply is assumed here. -/
structure Ready (F : Helpers) (r : TermCutRequest) (σ : WState F.ns 8) : Prop where
  loaded : ∀j : Fin 13,σ.st (F.loader (Fin.castAdd 1 j))=r.loadedSource j
  context : σ.st (F.data 14)=frame r.contextWord
  degree : σ.st (F.data 15)=frame (natWord r.degree)
  output : σ.st (F.data 16)=[]
  widthRuler : σ.st (F.data 20)=List.replicate (F.widthBudget r.stackWidth) false
  rowRuler : σ.st (F.data 21)=List.replicate (F.rowBudget (rowRequest r)) false
  zeroRuler : σ.st (F.data 22)=List.replicate
    (F.coefficientBudget (CoefficientRequest.mk (r.stackWidth+1) 0)) false
  oneRuler : σ.st (F.data 23)=List.replicate
    (F.coefficientBudget (CoefficientRequest.mk (r.stackWidth+1) 1)) false
  heads : ∀i,σ.sh i=0
  registers : ∀i,σ.val i=0

/-- `lem:print`, paper/paper.tex: one
actual private-bank helper call preserves the complete retained data
and finite rulers, as well as global scratch and reset heads. -/
theorem Ready.of_docked {F : Helpers} {r : TermCutRequest} {σ τ : WState F.ns 8}
    {t : ℕ} {bank : Fin t→Fin (F.ns+1)} {out : Fin t→List Bool}
    (h : Ready F r σ) (hd : Docked bank σ τ (fun _=>0) out)
    (hbd : ∀i j,bank i≠F.data j) : Ready F r τ := by
  have hdata : ∀j,τ.st (F.data j)=σ.st (F.data j) :=
    fun j=>(hd.other (F.data j) (fun i=>hbd i j)).1
  refine ⟨?_,(hdata 14).trans h.context,(hdata 15).trans h.degree,
    (hdata 16).trans h.output,(hdata 20).trans h.widthRuler,(hdata 21).trans h.rowRuler,
    (hdata 22).trans h.zeroRuler,(hdata 23).trans h.oneRuler,
    docked_zero_heads hd h.heads,fun i=>(congrFun hd.val i).trans (h.registers i)⟩
  intro j
  exact (hdata ⟨j.val,by have hj:=j.isLt;omega⟩).trans (h.loaded j)

/-- `lem:print`, paper/paper.tex: a
later unvisited one-shot bank stays genuinely cold outside the bank
of the current real helper execution. -/
theorem cold_after_docked {ns nr t u : ℕ} {σ τ : WState ns nr}
    {bank : Fin t→Fin (ns+1)} {other : Fin u→Fin (ns+1)} {out : Fin t→List Bool}
    (hd : Docked bank σ τ (fun _=>0) out) (hsep : ∀i j,bank i≠other j)
    (hcold : ∀j,σ.st (other j)=[]) : ∀j,τ.st (other j)=[] :=
  fun j=>((hd.other (other j) (fun i=>hsep i j)).1).trans (hcold j)

end NearQuarticWires.StageTupleSetupCold
