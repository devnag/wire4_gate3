import Proof.Quartic.StageFormulaMetadata.CountedNatural

set_option autoImplicit false

namespace NearQuarticWires.StageFormulaMetadata

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open StageLift

/-- `lem:print`, paper/paper.tex: decode and
count one unchanged atom-index or power-exponent source field. -/
def readCountedNatural (printing : Bool) (source : Fin VV) : St VV MM :=
  .seq (readTrackedNatural 0 source) (countedNatural printing source)

/-- `prop:time`, paper/paper.tex: the physical
field pipeline preserves the original packet and all unrelated stores,
while advancing only its paid input and normalized-output counters. -/
theorem readCountedNatural_spec (C : Ctx) (printing : Bool) (source : Fin VV)
    (hs : source∉[vZ,v1,v2,consumedVar,fieldBytesVar,aw0,emittedLengthVar,
      t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,vJ])
    (a : DS VV MM) (hc : Cst a) (bits : List Bool)
    (ha : a.ram 0=bits.map Bool.toNat) (value : ℕ) (rest : List Bool)
    (hin : bits.drop (a.rc 0)=natWord value++rest)
    (hwidth : natBitLength value+2≤C.Wd)
    (hinput : a.env consumedVar+(natWord value).length<2^C.Wd)
    (houtput : a.env emittedLengthVar+(natWord value).length<2^C.Wd) :
    Hs C (readCountedNatural printing source) a (80*natBitLength value+111) (fun b=>
      b.env source=value ∧
      b.env consumedVar=a.env consumedVar+(natWord value).length ∧
      b.env emittedLengthVar=a.env emittedLengthVar+(natWord value).length ∧
      b.out=a.out++(if printing then natWord value else []) ∧
      b.ip=a.ip ∧ b.ram=a.ram ∧ b.rc 0=a.rc 0+(natWord value).length ∧
      (∀ store,store≠0→b.rc store=a.rc store) ∧
      (b.kin,b.kout,b.kc)=(a.kin,a.kout,a.kc) ∧ Cst b ∧
      Fr a b (source::[consumedVar,fieldBytesVar,aw0,emittedLengthVar,
        t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,vJ])) := by
  have hsRead : source∉vZ::v1::v2::consumedVar::fieldBytesVar::rdNatT := by
    intro h
    apply hs
    simp only [rdNatT,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    tauto
  have hsPrint : source∉[aw0,fieldBytesVar,emittedLengthVar,t3,t5,t6,t7,t8,t9,vJ] := by
    intro h
    apply hs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    tauto
  have hsLength : emittedLengthVar≠source := by
    intro h
    subst source
    exact hs (by decide)
  unfold readCountedNatural
  refine (Hs.seq (t2:=50*natBitLength value+70)
    (readTrackedNatural_spec C 0 bits a hc ha source hsRead value rest hin hwidth hinput)
    fun b ⟨hbv,_hbl,hbi,hbrc,hbr,hbc,hbf⟩=>?_).mono (by omega) (fun _ h=>h)
  have hboff : b.env emittedLengthVar=a.env emittedLengthVar :=
    hbf _ (by simp (config:={decide:=true}) [hsLength])
  have hbscratch : source∉[aw0,fieldBytesVar,emittedLengthVar,t3,t5,t6,t7,t8,t9,vJ] := hsPrint
  have hW : 2≤C.Wd := by omega
  have e:=countedNatural_spec C printing source hbscratch b hbc hW (by rw [hbv,hboff];exact houtput)
  rw [hbv] at e
  refine e.mono le_rfl ?_
  rintro d ⟨hdlen,hdo,hdrest,hdc,hdf⟩
  simp only [memorySourceRest,Prod.mk.injEq] at hbr
  rcases hbr with ⟨hbip,hbout,hbram,hbrcursor,hbkin,hbkout,hbkc⟩
  simp only [Prod.mk.injEq] at hdrest
  rcases hdrest with ⟨hdip,hdram,hdrc,hdkin,hdkout,hdkc⟩
  refine ⟨?_,?_,by rw [hdlen,hboff],by rw [hdo,hbout],hdip.trans hbip,hdram.trans hbram,
    by rw [hdrc,hbrc],?_,by rw [hdkin,hdkout,hdkc,hbkin,hbkout,hbkc],hdc,?_⟩
  · rw [hdf source hsPrint,hbv]
  · rw [hdf _ (by decide),hbi]
  · intro store hstore
    rw [hdrc]
    have hcursor:=congrFun hbrcursor store
    simpa only [Function.update_of_ne hstore] using hcursor
  · exact (hbf.weaken (by
      intro target ht
      simp only [rdNatT,List.mem_cons,List.not_mem_nil,or_false] at ht ⊢
      tauto)).trans (hdf.weaken (by
        intro target ht
        simp only [List.mem_cons,List.not_mem_nil,or_false] at ht ⊢
        tauto))

end NearQuarticWires.StageFormulaMetadata
