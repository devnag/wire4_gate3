import Proof.Quartic.StageMainMask.EntryAcquire
import Proof.Quartic.StageGamma.ReadFields

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open StageMain StagePullback

/-- Step 4 of `sec:algorithm` and `imp:seed`, paper/paper.tex: the original column and actual projected field
value are decoded after the finite preparation source and W1 reader. -/
def readEntryIndices : St VV MM :=
  .seq (StageGamma.readFields [32, 34]) (.op (.copy 24 StagePrint.Header.translation))

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
these are the exact source-derived numeric indices and translation
retained for original-point construction. -/
structure EntryIndices {B1 B2 : ℕ} (r : EntryRequest B1 B2) (a : DS VV MM) : Prop where
  source : EntrySourceData r a
  column : a.env 32 = r.column.val
  fieldValue : a.env 34 = r.fieldValue.val
  translation : a.env 24 = translationNumber (entryPointRequest r false false).parameters
    (entryPointRequest r false false).translation

/-- Step 4 of `sec:algorithm`, `imp:seed` and `prop:time`,
paper/paper.tex: both actual
binary suffix fields and the physically computed witness translation
are retained with exact source/cursor semantics. -/
theorem readEntryIndices_run {B1 B2 : ℕ} (C : Ctx) (r : EntryRequest B1 B2)
    (rest : List Bool) (a : DS VV MM) (hc : Cst a) (ha : EntrySourceData r a)
    (hin : C.inp.drop a.ip = natWord r.column.val ++ natWord r.fieldValue.val ++ rest)
    (hwidth : natBitLength r.column.val + 2 ≤ C.Wd ∧ natBitLength r.fieldValue.val + 2 ≤ C.Wd) :
    Hs C readEntryIndices a (StageGamma.readFieldsCost [r.column.val, r.fieldValue.val] + 2)
      (fun b => EntryIndices r b ∧
        b.ip = a.ip + (natWord r.column.val ++ natWord r.fieldValue.val).length ∧
        b.out = a.out ∧ Cst b ∧ b.ram = a.ram ∧
        (b.kin, b.kout, b.kc) = (a.kin, a.kout, a.kc)) := by
  have hread := StageGamma.readFields_spec C [32, 34] (by decide) (by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> decide)
    [r.column.val, r.fieldValue.val] rfl a hc rest
    (by simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc] using hin)
    (by intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl <;> tauto)
  unfold readEntryIndices
  refine Hs.seq (t2 := 1) hread ?_
  rintro b ⟨hbfields, hbip, hbrest, hbc, hbfr⟩
  have hbram : b.ram = a.ram := congrArg (fun t => t.2.1) hbrest
  have hbrc : b.rc = a.rc := congrArg (fun t => t.2.2.1) hbrest
  have hbout : b.out = a.out := congrArg (fun t => t.1) hbrest
  have hbtr : b.env StagePrint.Header.translation =
      translationNumber (entryPointRequest r false false).parameters
        (entryPointRequest r false false).translation := (hbfr _ (by decide)).trans ha.translation
  refine (hs_copy C 24 StagePrint.Header.translation b (by decide)).mono le_rfl ?_
  rintro d rfl
  have hdf : Fr b (b.set 24 (b.env StagePrint.Header.translation)) [24] := Fr.set b _ (by simp)
  have hdc : Cst (b.set 24 (b.env StagePrint.Header.translation)) := hbc.of_fr hdf (by decide)
  have hsource : EntrySourceData r (b.set 24 (b.env StagePrint.Header.translation)) := by
    refine ⟨hbram ▸ ha.originalCall, hbram ▸ ha.parameters, hbram ▸ ha.witness, ?_, ?_⟩
    · intro store
      change b.rc store ≤ (b.ram store).length
      rw [hbram, hbrc]
      exact ha.cursors store
    · exact (hdf _ (by decide)).trans hbtr
  have hbcol : b.env 32 = r.column.val := by
    simpa only [Fin.getElem_fin, List.getElem_cons_zero] using hbfields ⟨0, by decide⟩
  have hbval : b.env 34 = r.fieldValue.val := by
    simpa only [Fin.getElem_fin, List.getElem_cons_succ, List.getElem_cons_zero] using hbfields ⟨1, by decide⟩
  refine ⟨⟨hsource, (hdf _ (by decide)).trans hbcol, (hdf _ (by decide)).trans hbval,
    (DS.set_env_self _ _ _).trans hbtr⟩, ?_, hbout, hdc, hbram,
    congrArg (fun t => (t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2)) hbrest⟩
  simpa only [DS.set_ip, List.flatMap_cons, List.flatMap_nil, List.append_nil] using hbip

end NearQuarticWires.StageMainMask
