import Proof.Quartic.StageCertNative.PriceProjection
import Proof.Quartic.StageCertNative.HeaderSource

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells

theorem JobPrice.first {B1 B2 : ℕ} {f : TermJob B1 B2→ℕ} {d : ℕ}
    (h : JobPrice f d) : JobPrice (fun r=>f (firstJob r.base)) d := by
  obtain ⟨C,E,h⟩:=h
  exact ⟨C,E,fun r=>h (firstJob r.base)⟩

theorem price_commonWidth (B1 B2 : ℕ) :
    JobPrice (fun r : TermJob B1 B2=>commonWidth r.base) 0 :=
  (price_stackWidth B1 B2).first

theorem price_successor (B1 B2 : ℕ) :
    JobPrice (fun r : TermJob B1 B2=>successorBudget (commonWidth r.base)) 0 := by
  exact (price_commonWidth B1 B2).natWordLength.finite
    (((JobPrice.constant 300).mul (price_commonWidth B1 B2).natBits).add
      (JobPrice.constant 608)) StageRecovery.packetCallee VV MM

theorem price_geometryLength (B1 B2 : ℕ) :
    JobPrice (fun r : TermJob B1 B2=>(StagePrint.Context.geometryWord r.base.prepared).length) 0 := by
  refine (price_contextLength B1 B2).mono ?_
  intro r
  rw [←geometryProjection_word]
  change (geometryProjection r.base.prepared).target.length≤
    (geometryProjection r.base.prepared).word.length
  simp only [FieldProjectionRequest.word,List.length_append,frame_length]
  omega

theorem price_firstJobSource {B1 B2 : ℕ}
    (hbase : JobPrice (fun r : TermJob B1 B2=>r.base.baseWord.length) 0)
    (hc : JobPrice (fun r : TermJob B1 B2=>cachedSourceBudget r.base) 0)
    (hword : JobPrice (fun r : TermJob B1 B2=>(cachedSourceWord r.base).length) 0) :
    JobPrice (fun r : TermJob B1 B2=>firstJobSourceBudget r.base) 0 := by
  have hz : JobPrice (fun r : TermJob B1 B2=>zeroOrdinalBudget r.base) 0 :=
    hbase.finite (JobPrice.constant 30) StageRecovery.packetCallee VV MM
  have hzero : JobPrice (fun _ : TermJob B1 B2=>(natWord 0).length) 0 :=
    JobPrice.constant _
  exact hbase.framedPair hzero hword hz hc

/-- `prop:time`, paper/paper.tex: original
geometry and exact packing-width generation have the same fourth
occurrence-degree price as the complete actual source compiler. -/
theorem price_nativeFields {B1 B2 : ℕ}
    (hbase : JobPrice (fun r : TermJob B1 B2=>r.base.baseWord.length) 0)
    (hc : JobPrice (fun r : TermJob B1 B2=>cachedSourceBudget r.base) 0)
    (hword : JobPrice (fun r : TermJob B1 B2=>(cachedSourceWord r.base).length) 0)
    (hcontext : JobPrice (fun r : TermJob B1 B2=>baseContextBudget r.base) 0) :
    JobPrice (fun r : TermJob B1 B2=>nativeFieldsBudget r.base) 4 := by
  have hfirst:=price_firstJobSource hbase hc hword
  have hstack:=((((JobPrice.constant 4).mul hfirst).raise (by decide : 0≤4)).add
    ((JobPrice.constant 4).mul (price_jobStack B1 B2).first)).add
    ((JobPrice.constant 12).raise (by decide : 0≤4))
  have hpacked:=(((JobPrice.constant 4).mul hstack).add
    (((JobPrice.constant 4).mul (price_successor B1 B2)).raise (by decide : 0≤4))).add
    ((JobPrice.constant 12).raise (by decide : 0≤4))
  have hgeo:=(((JobPrice.constant 4).mul hcontext).add
    ((JobPrice.constant 4).mul (price_geometryProjection B1 B2))).add
    (JobPrice.constant 12)
  exact (hbase.raise (by decide : 0≤4)).framedPair
    ((price_geometryLength B1 B2).raise (by decide : 0≤4))
    ((((price_commonWidth B1 B2).add (JobPrice.constant 1)).natWordLength).raise
      (by decide : 0≤4))
    (hgeo.raise (by decide : 0≤4)) hpacked

end NearQuarticWires.StageCertNative
