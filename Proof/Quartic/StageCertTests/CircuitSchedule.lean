import Proof.Quartic.StageCertTests.CircuitLimit

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertTests

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

/-- `sec:algorithm`, paper/paper.tex:
the actual active circuit count orders complete sign-filtered
whole-test metadata blocks by the original circuit index. -/
noncomputable def circuitMetadataForLimit (p : Cells.Parameters) (count : ℕ) (hc : count ≤ 2) :
    List TestMetadata :=
  (List.ofFn fun j : Fin count => circuitMetadataList p ⟨j.val,lt_of_lt_of_le j.isLt hc⟩).flatten

/-- `sec:algorithm`, paper/paper.tex:
the actual outer circuit loop invokes the complete sign scheduler. -/
def circuitLoop : St VV MM := forS testCircuitVar circuitLimitVar signSchedule

/-- `sec:algorithm`, paper/paper.tex:
the outer circuit loop retains all unrelated call and parameter registers. -/
def circuitScheduleScratch : List (Fin VV) :=
  testCircuitVar :: signLimitVar :: signOrdinal :: activePatternScratch

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: each original active circuit receives its
complete κ-filtered whole-test schedule in exact ordinal order. -/
theorem circuitLoop_spec (C : Ctx) (a : DS VV MM) (p : Cells.Parameters)
    (count B : ℕ) (hcount : count ≤ 2) (hc : Cst a)
    (hfields : ∀ field : ScheduleField, a.env field.variable = field.value p)
    (hlimit : a.env circuitLimitVar = count) (bounds : ScheduleBounds C p B) :
    Hs C circuitLoop a
      (count*(256*((p.J+1)*(56*p.k+200*B+310)+100)+604)+4) (fun b =>
      b.out = a.out ++ (circuitMetadataForLimit p count hcount).flatMap TestMetadata.word ∧
      (b.ip,b.ram,b.rc,b.kin,b.kout,b.kc) = (a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) ∧
      (∀ field : ScheduleField, b.env field.variable = field.value p) ∧ Cst b ∧
      Fr a b circuitScheduleScratch) := by
  let blocks := List.ofFn fun j : Fin count => circuitMetadataList p ⟨j.val,lt_of_lt_of_le j.isLt hcount⟩
  have hl : blocks.length = count := List.length_ofFn
  let I : ℕ → DS VV MM → Prop := fun k b =>
    b.out = a.out ++ (blocks.take k).flatMap (fun metadata => metadata.flatMap TestMetadata.word) ∧
    (b.ip,b.ram,b.rc,b.kin,b.kout,b.kc) = (a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) ∧
    (∀ field : ScheduleField, b.env field.variable = field.value p) ∧ Cst b ∧
    Fr a b circuitScheduleScratch
  have hfit : count < 2^C.Wd := by have := bounds.small;omega
  unfold circuitLoop
  refine (forS_spec' testCircuitVar circuitLimitVar (by decide) signSchedule a count hfit I
    (256*((p.J+1)*(56*p.k+200*B+310)+100)+600)
    (fun k b v ⟨hbo,hbr,hbf,hbc,hbfr⟩ => ?_)
    ⟨by simp,rfl,hfields,hc,Fr.refl _ _⟩ hlimit ?_).mono le_rfl ?_
  · refine ⟨hbo,hbr,?_,Cst.of_fr (T := [testCircuitVar]) hbc (Fr.set _ _ (by decide)) (by decide),
      Fr.trans hbfr (Fr.set _ _ (by simp [circuitScheduleScratch]))⟩
    intro field
    simpa (config := {decide := true}) [DS.set,show field.variable ≠ testCircuitVar by cases field <;> decide] using hbf field
  · intro k hk b ⟨hbo,hbr,hbf,hbc,hbfr⟩ hbctr hbn
    have hk2 : k < 2 := lt_of_lt_of_le hk hcount
    refine (signSchedule_spec C b p ⟨k,hk2⟩ B hbc hbf hbctr bounds).mono le_rfl ?_
    rintro d ⟨hdo,hdr,hdf,hdj,hdc,hdfr⟩
    have hkb : k < blocks.length := by omega
    have hblock : blocks[k] = circuitMetadataList p ⟨k,hk2⟩ := by simp only [blocks,List.getElem_ofFn]
    refine ⟨⟨?_,hdr.trans hbr,hdf,hdc,
      Fr.trans hbfr (Fr.weaken hdfr (by intro x hx;exact List.mem_cons_of_mem _ hx))⟩,
      hdj,by rw [hdfr _ (by decide),hbn]⟩
    rw [hdo,hbo,List.take_succ_eq_append_getElem hkb,List.flatMap_append,List.flatMap_singleton,
      hblock,List.append_assoc]
  · rintro b ⟨⟨hbo,hbr,hbf,hbc,hbfr⟩,_,_⟩
    refine ⟨?_,hbr,hbf,hbc,hbfr⟩
    rw [List.take_of_length_le (by omega : blocks.length ≤ count)] at hbo
    simpa only [circuitMetadataForLimit,blocks,List.flatten_eq_flatMap,List.flatMap_assoc,id_eq] using hbo

/-- `sec:algorithm`, paper/paper.tex:
the actual call tag selects the active circuit count before the
complete nested whole-test schedule is printed. -/
def allCircuitSchedule : St VV MM := .seq setCircuitLimit circuitLoop

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: actual call-kind branching and both
nested loops are charged without an assumed test-plan supplier. -/
theorem allCircuitSchedule_spec (C : Ctx) (a : DS VV MM) (p : Cells.Parameters)
    (kind : CallKind) (B : ℕ) (hc : Cst a)
    (hfields : ∀ field : ScheduleField, a.env field.variable = field.value p)
    (hk : a.env scheduleCallKindVar = kindTag kind) (bounds : ScheduleBounds C p B) :
    Hs C allCircuitSchedule a
      (2*(256*((p.J+1)*(56*p.k+200*B+310)+100)+604)+20) (fun b =>
      b.out = a.out ++ (circuitMetadataForLimit p (callCircuitCount kind)
        (callCircuitCount_bounds kind).2).flatMap TestMetadata.word ∧
      (b.ip,b.ram,b.rc,b.kin,b.kout,b.kc) = (a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) ∧
      (∀ field : ScheduleField, b.env field.variable = field.value p) ∧ Cst b ∧
      Fr a b (circuitLimitVar :: circuitScheduleScratch)) := by
  unfold allCircuitSchedule
  refine (Hs.seq (t2 := (callCircuitCount kind)*(256*((p.J+1)*(56*p.k+200*B+310)+100)+604)+4)
    (setCircuitLimit_spec C a kind hc hk (by have := bounds.small;omega))
    fun b ⟨hbl,hbsh,hbc,hbfr⟩ => ?_).mono (by
      have h := Nat.mul_le_mul_right (256*((p.J+1)*(56*p.k+200*B+310)+100)+604)
        (callCircuitCount_bounds kind).2
      omega) (fun _ h => h)
  have hbfields : ∀ field : ScheduleField, b.env field.variable = field.value p := by
    intro field
    rw [hbfr _ (by cases field <;> decide),hfields]
  refine (circuitLoop_spec C b p (callCircuitCount kind) B (callCircuitCount_bounds kind).2
    hbc hbfields hbl bounds).mono le_rfl ?_
  rintro d ⟨hdo,hdr,hdf,hdc,hdfr⟩
  have hbm := Same.of_sh hbsh
  have hrest : (b.ip,b.ram,b.rc,b.kin,b.kout,b.kc) = (a.ip,a.ram,a.rc,a.kin,a.kout,a.kc) := by
    simp only [Prod.mk.injEq]
    exact ⟨hbm.ip,hbm.ram,hbm.rc,hbm.kin,hbm.kout,hbm.kc⟩
  exact ⟨by rw [hdo,hbm.out],hdr.trans hrest,hdf,hdc,
    Fr.trans (Fr.weaken hbfr (by decide))
      (Fr.weaken hdfr (by intro x hx;exact List.mem_cons_of_mem _ hx))⟩

end NearQuarticWires.StageCertTests
