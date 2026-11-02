import Proof.Quartic.StageCertTests.ActivePattern

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertTests

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells

/-- `sec:cycle`, paper/paper.tex:
the exact binary sign enumeration consists of 256 ordered blocks,
with an empty block precisely at zero κ weight. -/
noncomputable def circuitMetadataBlocks (p : Cells.Parameters) (j : Fin 2) : List (List TestMetadata) :=
  List.ofFn fun code : Fin 256 => activePatternMetadata p j code

/-- `sec:algorithm`, paper/paper.tex:
one circuit's whole-test metadata concatenate the required sign blocks. -/
noncomputable def circuitMetadataList (p : Cells.Parameters) (j : Fin 2) : List TestMetadata :=
  (circuitMetadataBlocks p j).flatten

/-- `sec:cycle`, paper/paper.tex:
the physical ordinal loop retains its constant binary enumeration bound. -/
def signLimitVar : Fin VV := ⟨85,by decide⟩

/-- `sec:algorithm`, paper/paper.tex:
the sign loop physically checks κ and prints every required block. -/
def signLoop : St VV MM := forS signOrdinal signLimitVar activePatternSchedule

/-- `sec:algorithm`, paper/paper.tex:
the complete circuit scheduler constructs its actual fixed bound
before scanning all binary sign ordinals. -/
def signSchedule : St VV MM := .seq (setK signLimitVar 256) signLoop

/-- `sec:cycle` and `prop:time`, paper/paper.tex: the actual binary loop emits exactly the complete
required sign-filtered metadata sequence, with all loop operations paid. -/
theorem signLoop_spec (C : Ctx) (a : DS VV MM) (p : Cells.Parameters)
    (j : Fin 2) (B : ℕ) (hc : Cst a)
    (hfields : ∀ field : ScheduleField, a.env field.variable = field.value p)
    (hj : a.env testCircuitVar = j.val) (hlimit : a.env signLimitVar = 256)
    (bounds : ScheduleBounds C p B) :
    Hs C signLoop a (256*((p.J+1)*(56*p.k+200*B+310)+94)+4) (fun b =>
      b.out = a.out ++ (circuitMetadataList p j).flatMap TestMetadata.word ∧
      (b.ip,b.ram,b.rc,b.kin,b.kout,b.kc) = (a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) ∧
      (∀ field : ScheduleField, b.env field.variable = field.value p) ∧
      b.env testCircuitVar = j.val ∧ Cst b ∧ Fr a b (signOrdinal :: activePatternScratch)) := by
  let blocks := circuitMetadataBlocks p j
  have hl : blocks.length = 256 := List.length_ofFn
  let I : ℕ → DS VV MM → Prop := fun k b =>
    b.out = a.out ++ (blocks.take k).flatMap (fun metadata => metadata.flatMap TestMetadata.word) ∧
    (b.ip,b.ram,b.rc,b.kin,b.kout,b.kc) = (a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) ∧
    (∀ field : ScheduleField, b.env field.variable = field.value p) ∧
    b.env testCircuitVar = j.val ∧ Cst b ∧ Fr a b (signOrdinal :: activePatternScratch)
  unfold signLoop
  refine (forS_spec' signOrdinal signLimitVar (by decide) activePatternSchedule a 256 bounds.small I
    ((p.J+1)*(56*p.k+200*B+310)+90)
    (fun k b v ⟨hbo,hbr,hbf,hbj,hbc,hbfr⟩ => ?_)
    ⟨by simp,rfl,hfields,hj,hc,Fr.refl _ _⟩ hlimit ?_).mono le_rfl ?_
  · refine ⟨hbo,hbr,?_,?_,Cst.of_fr (T := [signOrdinal]) hbc (Fr.set _ _ (by decide)) (by decide),
      Fr.trans hbfr (Fr.set _ _ (by simp))⟩
    · intro field
      simpa (config := {decide := true}) [DS.set,show field.variable ≠ signOrdinal by cases field <;> decide] using hbf field
    · simpa (config := {decide := true}) [DS.set] using hbj
  · intro k hk b ⟨hbo,hbr,hbf,hbj,hbc,hbfr⟩ hbctr hbn
    refine (activePatternSchedule_spec C b p j ⟨k,hk⟩ B hbc hbf hbj hbctr bounds).mono le_rfl ?_
    rintro d ⟨hdo,hdr,hdf,hdj,hds,hdc,hdfr⟩
    have hkb : k < blocks.length := by omega
    have hblock : blocks[k] = activePatternMetadata p j ⟨k,hk⟩ := by
      simp only [blocks,circuitMetadataBlocks,List.getElem_ofFn]
    refine ⟨⟨?_,hdr.trans hbr,hdf,hdj,hdc,
      Fr.trans hbfr (Fr.weaken hdfr (by intro x hx;exact List.mem_cons_of_mem _ hx))⟩,
      hds,by rw [hdfr _ (by decide),hbn]⟩
    rw [hdo,hbo,List.take_succ_eq_append_getElem hkb,List.flatMap_append,List.flatMap_singleton,
      hblock,List.append_assoc]
  · rintro b ⟨⟨hbo,hbr,hbf,hbj,hbc,hbfr⟩,_,_⟩
    refine ⟨?_,hbr,hbf,hbj,hbc,hbfr⟩
    rw [List.take_of_length_le (by omega : blocks.length ≤ 256)] at hbo
    simpa only [circuitMetadataList,blocks,List.flatten_eq_flatMap,List.flatMap_assoc,id_eq] using hbo

/-- `sec:cycle` and `prop:time`, paper/paper.tex: the constant-bound initializer and complete sign
schedule have a fully charged physical source clock. -/
theorem signSchedule_spec (C : Ctx) (a : DS VV MM) (p : Cells.Parameters)
    (j : Fin 2) (B : ℕ) (hc : Cst a)
    (hfields : ∀ field : ScheduleField, a.env field.variable = field.value p)
    (hj : a.env testCircuitVar = j.val) (bounds : ScheduleBounds C p B) :
    Hs C signSchedule a (256*((p.J+1)*(56*p.k+200*B+310)+100)+600) (fun b =>
      b.out = a.out ++ (circuitMetadataList p j).flatMap TestMetadata.word ∧
      (b.ip,b.ram,b.rc,b.kin,b.kout,b.kc) = (a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) ∧
      (∀ field : ScheduleField, b.env field.variable = field.value p) ∧
      b.env testCircuitVar = j.val ∧ Cst b ∧
      Fr a b (signLimitVar :: signOrdinal :: activePatternScratch)) := by
  unfold signSchedule
  refine (Hs.seq (t2 := 256*((p.J+1)*(56*p.k+200*B+310)+94)+4)
    (setK_spec signLimitVar (by decide) 256 a bounds.small)
    fun b ⟨hbl,hbsh,hbfr⟩ => ?_).mono (by omega) (fun _ h => h)
  have hbc : Cst b := Cst.of_fr hc hbfr (by decide)
  have hbfields : ∀ field : ScheduleField, b.env field.variable = field.value p := by
    intro field
    rw [hbfr _ (by cases field <;> decide),hfields]
  have hbj : b.env testCircuitVar = j.val := by rw [hbfr _ (by decide),hj]
  refine (signLoop_spec C b p j B hbc hbfields hbj hbl bounds).mono le_rfl ?_
  rintro d ⟨hdo,hdr,hdf,hdj,hdc,hdfr⟩
  have hbm := Same.of_sh hbsh
  have hrest : (b.ip,b.ram,b.rc,b.kin,b.kout,b.kc) = (a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) := by
    simp only [Prod.mk.injEq]
    exact ⟨hbm.ip,hbm.ram,hbm.rc,hbm.kin,hbm.kout,hbm.kc⟩
  refine ⟨by rw [hdo,hbm.out],hdr.trans hrest,hdf,hdj,hdc,
    Fr.trans (Fr.weaken hbfr (by decide))
      (Fr.weaken hdfr (by intro x hx;exact List.mem_cons_of_mem _ hx))⟩

end NearQuarticWires.StageCertTests
