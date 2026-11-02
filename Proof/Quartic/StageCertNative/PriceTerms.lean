import Proof.Quartic.StageCertNative.PriceSource
import Proof.Quartic.StageCertNative.FramingCost
import Proof.Quartic.StageCertNative.EntryRequest

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats
open StageCert.Tokens

noncomputable def jobPoolArity {B1 B2 : ℕ} (r : TermJob B1 B2) : ℕ :=
  17*(Builder.allGates r.moment.call).length

noncomputable def jobCoefficientBits {B1 B2 : ℕ} (r : TermJob B1 B2) : ℕ :=
  Cells.nativeCertificateBits B1 r.moment.call.n

theorem price_poolArity (B1 B2 : ℕ) : JobPrice (@jobPoolArity B1 B2) 0 := by
  refine JobPrice.of_arity ⟨34,4,fun r=>?_⟩
  exact (StageCertSourceBounds.actual_pool_arity_le r.moment).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ _) _))

theorem price_coefficientBits (B1 B2 : ℕ) : JobPrice (@jobCoefficientBits B1 B2) 0 := by
  refine JobPrice.of_arity ⟨entryScaleCoefficient B1 B2,entryScaleExponent B1 B2,fun r=>?_⟩
  exact (show jobCoefficientBits r≤entryScale r by unfold jobCoefficientBits entryScale;omega).trans
    (entryScale_arity r)

noncomputable def jobRecordHeight {B1 B2 : ℕ} (r : TermJob B1 B2) : ℕ :=
  StageGreedyEntryBounds.recordHeight (jobPoolArity r) (jobCoefficientBits r)

theorem price_recordHeight (B1 B2 : ℕ) : JobPrice (@jobRecordHeight B1 B2) 0 := by
  have hV:=price_poolArity B1 B2
  have hb:=price_coefficientBits B1 B2
  have h2V:=((JobPrice.constant 2).mul hV).add (JobPrice.constant 3)
  have h2b:=((JobPrice.constant 2).mul hb).add (JobPrice.constant 3)
  exact ((h2V.add (hV.mul h2V)).add (JobPrice.constant 5)).add h2b

theorem price_termsCount (B1 B2 : ℕ) :
    JobPrice (fun r : TermJob B1 B2=>(exactTerms r.moment).length) 1 := by
  refine ⟨1,0,fun r=>?_⟩
  let e:=exactEntry r.moment
  have hh:=Terms.length_le e.degree e.terms e.terms_nodup e.terms_degree
  have hs:=sum_choose_mul_pow_le (jobPoolArity r) e.degree 1
  simp only [one_pow,Nat.mul_one] at hs
  have hbase : 1+jobPoolArity r≤r.moment.selected.1.Uocc := by
    have ho:=r.moment.source_occurrence_guard
    unfold jobPoolArity
    omega
  have hb:=Nat.pow_le_pow_left hbase e.degree
  have h:=hh.trans (hs.trans hb)
  change (exactTerms r.moment).length≤
    r.moment.selected.1.Uocc^r.moment.packet.degree at h
  simpa only [pow_zero,mul_one,one_mul] using h

private theorem termsWord_length_bound {V : ℕ} (P : Terms V) (bits : ℕ)
    (hc : ∀t∈P,t.2.natAbs<2^bits) :
    (termsWord P).length≤P.length*(StageGreedyEntryBounds.recordHeight V bits+2)+3 := by
  have hh:=NearCubicGates.Close.Expand.Layout.natWord_len_le P.length P.length Nat.lt_two_pow_self
  have hs:=List.sum_le_card_nsmul (P.map fun t=>(monoWord t).length)
    (StageGreedyEntryBounds.recordHeight V bits) (by
      intro v hv
      obtain ⟨t,ht,rfl⟩:=List.mem_map.mp hv
      exact StageGreedyEntryBounds.monoWord_length V bits t (hc t ht))
  simp only [List.length_map,smul_eq_mul] at hs
  simp only [termsWord,NearCubicGates.Close.Interfaces.listWord,List.length_append,List.length_flatMap]
  nlinarith only [hh,hs]

theorem price_termsWord (B1 B2 : ℕ) :
    JobPrice (fun r : TermJob B1 B2=>(termsWord (exactTerms r.moment)).length) 1 := by
  have hR:=(price_recordHeight B1 B2).add (JobPrice.constant 2)
  have hm:=(price_termsCount B1 B2).mul hR
  have hb:=hm.add ((JobPrice.constant 3).raise (by decide : 0≤1))
  refine hb.mono ?_
  intro r
  exact termsWord_length_bound _ (jobCoefficientBits r) (fun t ht=>
    (r.moment.expansion_coefficient_bits t ht).1)

theorem price_termsFramer (B1 B2 : ℕ) :
    JobPrice (fun r : TermJob B1 B2=>NearCubicGates.Close.Expand.PolyTab.cpTermsCost (exactTerms r.moment)) 1 := by
  have hS:=((price_poolArity B1 B2).add (price_coefficientBits B1 B2)).add (JobPrice.constant 10)
  have hpoly:=(JobPrice.constant 100000).mul (hS.pow 4)
  have hsize:=((price_termsCount B1 B2).add (price_termsWord B1 B2)).add
    ((JobPrice.constant 1).raise (by decide : 0≤1))
  have hb:=hpoly.mul hsize
  refine hb.mono ?_
  intro r
  exact cpTermsCost_bits _ (exactEntry r.moment).terms_nodup (fun t ht=>
    (r.moment.expansion_coefficient_bits t ht).1)

theorem price_framedExpansion (B1 B2 : ℕ) :
    JobPrice (fun r : TermJob B1 B2=>2*expandFrameSteps
      NearCubicGates.Close.Expand.expansionMachine ⟨r.moment.packet.arity,r.moment.formula⟩+2) 3 := by
  have he:=(JobPrice.constant 2).mul (price_expansionCost B1 B2)
  have hc:=(price_termsFramer B1 B2).raise (by decide : 1≤3)
  have hs:=(he.add hc).add ((JobPrice.constant 3).raise (by decide : 0≤3))
  exact ((JobPrice.constant 2).mul hs).add ((JobPrice.constant 2).raise (by decide : 0≤3))

end NearQuarticWires.StageCertNative
