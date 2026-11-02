import Proof.Quartic.StageCertTests.ScheduleFields

set_option autoImplicit false

namespace NearQuarticWires.StageCertTests

open NearCubicGates.Close.Cells

/-- `sec:params`, paper/paper.tex:
each required scheduling scalar is fetched by its exact sequential scan. -/
def loadScheduleFields : List ScheduleField → St VV MM
  | [] => skipS
  | field :: fields => .seq (selectParameter field.index field.variable) (loadScheduleFields fields)

/-- `sec:params` and `prop:time`, paper/paper.tex: all requested scalar fetches pay their full head
returns and preserve every original source and record word. -/
theorem loadScheduleFields_spec (fields : List ScheduleField) (C : Ctx) (a : DS VV MM)
    (p : Cells.Parameters) (hp : a.ram StageLift.parameterStore = StageLift.parameterScalars p)
    (hr : a.rc StageLift.parameterStore ≤ 46) :
    Hs C (loadScheduleFields fields) a (152*fields.length+1) (fun b =>
      (∀ field ∈ fields, b.env field.variable = field.value p) ∧
      b.rc StageLift.parameterStore ≤ 46 ∧ b.ram = a.ram ∧
      (b.ip,b.out,b.kin,b.kout,b.kc) = (a.ip,a.out,a.kin,a.kout,a.kc) ∧
      Fr a b (vJ :: fields.map ScheduleField.variable)) := by
  induction fields generalizing a with
  | nil =>
      refine (skip_spec (C := C) a).mono (by simp) ?_
      rintro b rfl
      exact ⟨by simp,hr,rfl,rfl,Fr.set _ _ (by simp)⟩
  | cons field fields ih =>
      unfold loadScheduleFields
      refine (Hs.seq (t2 := 152*fields.length+1) (selectScheduleField_spec C a p field hp hr)
        fun b ⟨hbv,hbrc,hbr,hbs,hbf⟩ => ?_).mono (by simp;omega) (fun _ h => h)
      refine (ih b (hbr ▸ hp) hbrc).mono le_rfl ?_
      rintro d ⟨hdv,hdrc,hdr,hds,hdf⟩
      refine ⟨?_,hdrc,hdr.trans hbr,hds.trans hbs,?_⟩
      · intro target ht
        rcases List.mem_cons.mp ht with he | hm
        · subst target
          by_cases hm : field ∈ fields
          · exact hdv field hm
          · rw [hdf _ ?_,hbv]
            simp only [List.mem_cons,List.mem_map]
            rintro (he | ⟨other,ho,he⟩)
            · cases field <;> cases he
            · exact hm ((ScheduleField.variable_injective he) ▸ ho)
        · exact hdv target hm
      · apply Fr.trans (Fr.weaken hbf ?_) (Fr.weaken hdf ?_)
        · intro x hx
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
          rcases hx with rfl | rfl <;> simp
        · intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · simp
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)

/-- `eq:testX`–`eq:testPhi` and `sec:params`, paper/paper.tex: these are all retained scalars needed by
the whole-test scheduler. -/
def scheduleFields : List ScheduleField :=
  [.k,.populationBase,.digitBase,.chainLength,.errorBase]

/-- `sec:params`, paper/paper.tex:
the fixed scalar loader physically supplies every threshold and
chain parameter from the exact shared parameter-store parser output. -/
theorem loadAllScheduleFields_spec (C : Ctx) (a : DS VV MM) (p : Cells.Parameters)
    (hp : a.ram StageLift.parameterStore = StageLift.parameterScalars p)
    (hr : a.rc StageLift.parameterStore ≤ 46) (hc : Cst a) :
    Hs C (loadScheduleFields scheduleFields) a 761 (fun b =>
      (∀ field : ScheduleField, b.env field.variable = field.value p) ∧
      b.ram = a.ram ∧ (b.ip,b.out,b.kin,b.kout,b.kc) = (a.ip,a.out,a.kin,a.kout,a.kc) ∧ Cst b ∧
      Fr a b (vJ :: scheduleFields.map ScheduleField.variable)) := by
  refine (loadScheduleFields_spec scheduleFields C a p hp hr).mono (by rfl) ?_
  rintro b ⟨hb,_,hbr,hbs,hbf⟩
  refine ⟨?_,hbr,hbs,Cst.of_fr hc hbf (by decide),hbf⟩
  intro field
  apply hb
  cases field <;> simp [scheduleFields]

end NearQuarticWires.StageCertTests
