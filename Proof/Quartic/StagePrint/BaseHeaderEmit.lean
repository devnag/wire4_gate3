import Proof.Quartic.StagePrint.BaseHeader
import Proof.Quartic.StagePrint.HeaderEmit

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.Header
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

/-- `imp:pullback` and `lem:print`, paper/paper.tex: the first seven native affine fields are common to all original children and walk roles. -/
def baseHeaderRegisters : List (Fin VV) :=
  [arity,Lin,Lout,blockCount,blockWidth,syndromeWidth,translation]

/-- `imp:pullback` and `lem:print`, paper/paper.tex: exact values of the common original affine header. -/
def baseHeaderValues (r : HeaderCall) : List ℕ :=
  [r.call.n,(4*r.call.n+1)*Nat.clog 2 (r.call.n+1)+5,
    (4*r.call.n+1)*Nat.clog 2 (r.call.n+1)+5+r.call.n+6,
    r.parameters.r,r.parameters.b,r.parameters.s,
    StagePullback.translationNumber
      (Builder.star r.call r.prepared)
      (Builder.translation r.call r.prepared r.witness)]

/-- `lem:print`, paper/paper.tex: the physically loaded register list equals the exact original header list. -/
theorem BaseHeaderData.values {r : HeaderCall}
    {a : DS VV MM} (h : BaseHeaderData r a) :
    baseHeaderRegisters.map a.env=baseHeaderValues r := by
  simp only [baseHeaderRegisters,baseHeaderValues,List.map_cons,List.map_nil,
    h.n,h.sourceWidth,h.targetWidth,h.r,h.b,h.s,h.translation]

/-- `lem:print`, paper/paper.tex: the actual retained original input and witness are read before the common native prefix is written. -/
def printBaseHeader : St VV MM := .seq baseHeaderProgram (emitHeaderFields baseHeaderRegisters)

/-- `lem:print` and `prop:time`, paper/paper.tex: common metadata are physically serialized once, preserving the complete source and memory. -/
theorem printBaseHeader_run (C : Ctx) (r : HeaderCall)
    (a : DS VV MM) (hc : Cst a) (ha : Valid C a) (hd : HeaderSourceData r a)
    (hWd : r.call.n+3≤C.Wd)
    (hcap : 4*(r.call.n+1)^2+r.call.n+20<2^C.Wd)
    (hf : ∀v∈baseHeaderValues r,natBitLength v+2<2^C.Wd) :
    Hs C printBaseHeader a
      (baseHeaderCost r.call r.parameters r.witness+
        headerEmitCost (baseHeaderValues r)+1)
      (fun b=>b.out=a.out++(baseHeaderValues r).flatMap natWord ∧
        b.ram=a.ram ∧ b.ip=a.ip ∧
        (b.kin,b.kout,b.kc)=(a.kin,a.kout,a.kc) ∧ Cst b ∧ Valid C b) := by
  unfold printBaseHeader
  refine Hs.seq (t2:=headerEmitCost (baseHeaderValues r))
    (baseHeaderProgram_run C r a hc ha hd hWd hcap) ?_
  rintro b ⟨bh,br,bi,bo,bs,bc,bv⟩
  have er:=emitHeaderFields_run C baseHeaderRegisters b bc (by omega)
    (by decide) (by
      intro x hx
      apply hf
      rw [←bh.values]
      exact List.mem_map.mpr ⟨x,hx,rfl⟩)
  rw [bh.values] at er
  refine (source_addValid (by omega) bv er).mono le_rfl ?_
  rintro d ⟨⟨do_,ds,dc,_df⟩,dv⟩
  refine ⟨?_,?_,?_,?_,dc,dv⟩
  · rw [do_,bo]
  · exact (congrArg (fun t=>t.2.1) ds).trans br
  · exact (congrArg (fun t=>t.1) ds).trans bi
  · exact (congrArg (fun t=>(t.2.2.2.1,t.2.2.2.2.1,t.2.2.2.2.2)) ds).trans bs

end NearQuarticWires.StagePrint.Header
