import Proof.Quartic.StagePrint.PrintTranslation
import Proof.Quartic.StageLift.PrintRequest

set_option autoImplicit false

namespace NearQuarticWires.StagePrint.Header
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

/-- `imp:partition` and `lem:print`, paper/paper.tex: the common affine header depends only on the original call, its actual prepared parameters and witness, independently of recovery indices. -/
structure HeaderCall where
  call : Call
  parameters : Cells.Parameters
  prepared : Cells.ParameterRules (Builder.callInput call) parameters
  witness : List Bool

/-- `lem:print`, paper/paper.tex: a recovery request retains precisely this same original affine-header source. -/
def HeaderCall.of_print {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : HeaderCall :=
  ⟨r.child.call,r.child.selected.1,Cells.prepare_spec _ r.child.selected.1 r.child.selected.2,r.child.witness⟩

/-- `lem:print`, paper/paper.tex: only the actual finite original call, retained scalar bytes and witness bits are used by the common header, regardless of the current source-reader cursors. -/
structure HeaderSourceData (r : HeaderCall)
    (a : DS VV MM) : Prop where
  originalCall : a.ram StageLift.callStore=(callWord r.call).map Bool.toNat
  scalarFields : a.ram StageLift.parameterStore=StageLift.parameterScalars r.parameters
  witnessBits : a.ram StageLift.witnessStore=
    (Program.witnessPrefix r.call r.parameters r.witness).map Bool.toNat

/-- `lem:print`, paper/paper.tex: the original complete source acquisition supplies the exact retained header bytes. -/
theorem HeaderSourceData.of_source {B1 B2 : ℕ} {r : Greedy.PrintRequest B1 B2}
    {a : DS VV MM} (h : StageLift.PrintSourceData r a) : HeaderSourceData (HeaderCall.of_print r) a :=
  ⟨h.originalCall,h.scalarFields,h.witnessBits⟩

/-- `lem:print`, paper/paper.tex: normalizing the actual printer index does not invalidate the retained original header source. -/
theorem HeaderSourceData.of_request {B1 B2 : ℕ} {r : Greedy.PrintRequest B1 B2}
    {a : DS VV MM} (h : StageLift.PrintRequestData r a) : HeaderSourceData (HeaderCall.of_print r) a :=
  ⟨h.originalCall,h.scalarFields,h.witnessBits⟩

/-- `imp:partition`, witness (W1) and `lem:print`, paper/paper.tex: the actual translation is decoded with every rewind charged from its current cursor, which validity bounds by the retained source length. -/
theorem readHeaderTranslation_run (C : Ctx) (r : HeaderCall)
    (a : DS VV MM) (hc : Cst a) (ha : Valid C a) (hd : HeaderSourceData r a)
    (hwidth : r.call.n+3≤C.Wd) :
    Hs C readTranslation a
      (106+translationCost (Program.witnessPrefix r.call r.parameters r.witness).length
        r.parameters.k)
      (fun b=>b.env translation=StagePullback.translationNumber
          (Builder.star r.call r.prepared)
          (Builder.translation r.call r.prepared
            r.witness) ∧
        b.ram=a.ram ∧ b.ip=a.ip ∧ b.out=a.out ∧
        (b.kin,b.kout,b.kc)=(a.kin,a.kout,a.kc) ∧ Cst b) := by
  let p:=r.parameters
  let hs:=r.prepared
  have hk : p.k<r.call.n := hs.k_lt_n
  have ef:=readTranslation_run C p
    (Program.witnessPrefix r.call p r.witness) a hc hd.scalarFields hd.witnessBits
    (by simp only [Program.witnessPrefix,List.length_ofFn,Program.witnessReadLength];omega)
    (Nat.pow_lt_pow_right (by decide) (by omega))
    (lt_of_lt_of_le (by norm_num : 7<2^3)
      (Nat.pow_le_pow_right (by decide) (by omega)))
  have hp : a.rc StageLift.parameterStore≤46 := by
    have h:=ha.rc_le StageLift.parameterStore
    simpa only [hd.scalarFields,StageLift.parameterScalars_length] using h
  have hw : a.rc StageLift.witnessStore≤
      (Program.witnessPrefix r.call p r.witness).length := by
    have h:=ha.rc_le StageLift.witnessStore
    simpa only [hd.witnessBits,List.length_map] using h
  refine ef.mono ?_ ?_
  · dsimp only [translationCost]
    nlinarith
  · rintro b ⟨bv,br,bi,bo,bs,bc⟩
    exact ⟨bv.trans (translationNumber_retained r.call hs r.witness).symm,
      br,bi,bo,bs,bc⟩

end NearQuarticWires.StagePrint.Header
