import Proof.Quartic.StageMainMask.EntryIndices
import Proof.Quartic.StagePrint.CallArityMemory

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageMain StageLift

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
the actual original call's leading arity is read physically and copied
into the canonical point encoder's source variable. -/
def readEntryArity : St VV MM :=
  .seq StagePrint.Header.readCallArity (.op (.copy 20 StagePrint.Header.arity))

/-- Step 4 of `sec:algorithm` and `prop:time`, paper/paper.tex: the point dimension comes from the actual
retained original-call bytes, with a paid rewind, field read and copy. -/
theorem readEntryArity_run {B1 B2 : ℕ} (C : Ctx) (r : EntryRequest B1 B2)
    (a : DS VV MM) (hc : Cst a) (ha : EntryIndices r a)
    (hwidth : natBitLength r.call.n + 2 ≤ C.Wd) :
    Hs C readEntryArity a
      ((callWord r.call).length + 30 * natBitLength r.call.n + 42) (fun b =>
        b.env 20 = r.call.n ∧ EntryIndices r b ∧ b.ip = a.ip ∧ b.out = a.out ∧ Cst b ∧
        Fr a b (20 :: StagePrint.Header.arity :: rdNatT) ∧ b.ram = a.ram ∧
        (b.kin, b.kout, b.kc) = (a.kin, a.kout, a.kc)) := by
  have hcall : a.rc callStore ≤ (callWord r.call).length := by
    simpa only [ha.source.originalCall, List.length_map] using ha.source.cursors callStore
  obtain ⟨b, n, he, hn, hbvalue, hbip, hbout, hbram, _hbstreams, hbc, hbfr⟩ :=
    StagePrint.Header.readCallArity_run C r.call a hc ha.source.originalCall hwidth
  have hbcursor := he.rc_le ha.source.cursors
  unfold readEntryArity
  refine (Hs.seq (t1 := (callWord r.call).length + 30 * natBitLength r.call.n + 40)
    (t2 := 1) (show Hs C StagePrint.Header.readCallArity a
      ((callWord r.call).length + 30 * natBitLength r.call.n + 40) (· = b) from
        ⟨b, n, he, by omega, rfl⟩) ?_)
  intro d heq
  subst d
  refine (hs_copy C 20 StagePrint.Header.arity b (by decide)).mono le_rfl ?_
  rintro d rfl
  have hdf : Fr b (b.set 20 (b.env StagePrint.Header.arity)) [20] := Fr.set b _ (by simp)
  have hdc : Cst (b.set 20 (b.env StagePrint.Header.arity)) := hbc.of_fr hdf (by decide)
  have hsource : EntrySourceData r (b.set 20 (b.env StagePrint.Header.arity)) :=
    ⟨hbram ▸ ha.source.originalCall, hbram ▸ ha.source.parameters, hbram ▸ ha.source.witness,
      hbcursor, (hdf _ (by decide)).trans ((hbfr _ (by decide)).trans ha.source.translation)⟩
  refine ⟨(DS.set_env_self _ _ _).trans hbvalue,
    ⟨hsource, (hdf _ (by decide)).trans ((hbfr _ (by decide)).trans ha.column),
      (hdf _ (by decide)).trans ((hbfr _ (by decide)).trans ha.fieldValue),
      (hdf _ (by decide)).trans ((hbfr _ (by decide)).trans ha.translation)⟩,
    hbip, hbout, hdc, ?_, hbram, _hbstreams⟩
  exact (hbfr.weaken (fun _ hx => List.mem_cons_of_mem _ hx)).trans (Fr.set b _ (by simp))

end NearQuarticWires.StageMainMask
