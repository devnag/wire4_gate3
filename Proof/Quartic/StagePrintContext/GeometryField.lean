import Proof.Quartic.StagePrintContext.HeaderField

set_option autoImplicit false

namespace NearQuarticWires.StagePrintContext

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open StagePrint.Header

/-- `imp:partition` and `lem:print`, paper/paper.tex: only the four actual original star scalars
are retained for the later physical canonical-column constructor. -/
def geometryRegisters : List (Fin VV) := [arity,blockCount,blockWidth,syndromeWidth]

/-- `lem:print`, paper/paper.tex: the final
nonempty context field is serialized from its physically loaded registers. -/
def emitGeometryField : St VV MM := framedFields geometryRegisters

/-- `lem:print` and `prop:time`, paper/paper.tex: original geometry is written once with its real frame,
without a supplied column list, child pool, or decoded geometry source. -/
theorem emitGeometryField_run (C : Ctx) (r : HeaderCall) (a : DS VV MM)
    (hc : Cst a) (hv : Valid C a) (hd : BaseHeaderData r a) (hW : 3≤C.Wd) :
    Hs C emitGeometryField a (3*fieldClock 4 C.Wd+2) (fun b=>
      b.out=a.out++frame ([r.call.n,r.parameters.r,r.parameters.b,r.parameters.s].flatMap
        NearCubicWires.RepairRepresentation.natWord) ∧b.ip=a.ip ∧b.ram=a.ram ∧
      (b.kin,b.kout,b.kc)=(a.kin,a.kout,a.kc) ∧Cst b ∧Valid C b) := by
  have hvalues : geometryRegisters.map a.env=[r.call.n,r.parameters.r,r.parameters.b,r.parameters.s] := by
    simp only [geometryRegisters,List.map_cons,List.map_nil,hd.n,hd.r,hd.b,hd.s]
  have hcst:=headerEmitCost_valid C geometryRegisters a hv (by omega)
  change StagePrint.Header.headerEmitCost (geometryRegisters.map a.env)≤fieldClock 4 C.Wd at hcst
  have er:=framedFields_run C geometryRegisters a hc hv hW (by decide)
  rw [hvalues] at er hcst
  refine er.mono (by omega) ?_
  rintro b ⟨bo,bi,br,_brc,bs,bc,bv,_bf⟩
  exact ⟨bo,bi,br,bs,bc,bv⟩

/-- `lem:print`, paper/paper.tex: fixed empty
context fields are emitted as real false delimiter bits. -/
def emitLiteral : List Bool→St VV MM
  | []=>skipS
  | bit::bits=>.seq (.op (.emit bit)) (emitLiteral bits)

/-- `lem:print` and `prop:time`, paper/paper.tex: every literal delimiter is physically written and charged. -/
theorem emitLiteral_run (C : Ctx) (bits : List Bool) (a : DS VV MM) :
    Hs C (emitLiteral bits) a (2*bits.length+1) (fun b=>b.out=a.out++bits) := by
  induction bits generalizing a with
  | nil=>
      refine (skip_spec (C:=C) a).mono (by simp) ?_
      rintro b rfl
      simp
  | cons bit bits ih=>
      unfold emitLiteral
      refine (Hs.seq (t2:=2*bits.length+1) (hs_emit (C:=C) bit a) ?_).mono (by simp;omega) (fun _ h=>h)
      rintro b rfl
      refine (ih {a with out:=a.out++[bit]}).mono le_rfl ?_
      intro z hz
      simpa only [List.append_assoc,List.singleton_append] using hz

end NearQuarticWires.StagePrintContext
