import Proof.Quartic.StagePrint.EntryRetain

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.GreedyEntry
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells StageFormulaMetadata

/-- `lem:print`, paper/paper.tex: the actual
finite field reader changes exactly one retained store and cursor,
with its measured length kept outside the input-byte scratch. -/
theorem retainField_full_run (C : Ctx) (store : Fin MM) (lengthVar : Fin VV)
    (hl : lengthVar∉[vZ,v1,v2,t0,t1,payloadLengthVar])
    (bits rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip=frame bits++rest)
    (hcursor : a.rc store=(a.ram store).length)
    (hfit : bits.length<2^C.Wd) :
    Hs C (retainField store lengthVar) a (10*bits.length+8) (fun b =>
      b.env lengthVar=bits.length ∧ b.env payloadLengthVar=bits.length ∧
      b.ip=a.ip+(frame bits).length ∧
      b.ram=Function.update a.ram store (a.ram store++bits.map Bool.toNat) ∧
      b.rc=Function.update a.rc store (a.rc store+bits.length) ∧
      (b.out,b.kin,b.kout,b.kc)=(a.out,a.kin,a.kout,a.kc) ∧
      Cst b ∧ Fr a b [t0,t1,payloadLengthVar,lengthVar]) := by
  refine (retainField_run C store lengthVar hl bits rest a hc hin hcursor hfit).mono le_rfl ?_
  rintro b ⟨bl,bp,bi,br,brc,bo,brest,bc,bfr⟩
  refine ⟨bl,bp,bi,?_,?_,brest,bc,bfr⟩
  · funext other
    by_cases h : other=store
    · subst other;simpa only [Function.update_self] using br
    · simpa only [Function.update_of_ne h] using (bo other h).1
  · funext other
    by_cases h : other=store
    · subst other;simpa only [Function.update_self] using brc
    · simpa only [Function.update_of_ne h] using (bo other h).2

end NearQuarticWires.StagePrint.GreedyEntry
