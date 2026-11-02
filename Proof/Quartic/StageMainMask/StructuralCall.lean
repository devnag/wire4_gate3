import Proof.Quartic.StageMainMask.EntryCallee
import Proof.Quartic.StageMainMask.StructuralWriter
import Proof.Quartic.StageMainMask.BitReply
import Proof.Quartic.StageMainMask.ReplyData

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open StageMain StageMain.Compact StageLift

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
the actual entry body has one shared fixed ordinary subroutine port
with native scalar width and explicit input and time reservations. -/
noncomputable def entryContext (B1 B2 width : ℕ) (input : List Bool) (L B : ℕ) : Ctx :=
  ⟨width, input, entryCallee B1 B2, L, B⟩

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
write the original structural source, execute its actual cold ordinary
machine and consume the complete three-bit singleton reply. -/
def structuralStep : St VV MM :=
  .seq emitStructuralInput (.seq (.op .kcall) (readBitReply structuralFlag))

/-- `def:mask`, Step 4 of `sec:algorithm` and `prop:time`,
paper/paper.tex:
the physical shared structural-source invocation returns the exact
original flag and preserves all actual original points and sources. -/
theorem structuralStep_run {B1 B2 : ℕ} (r : EntryRequest B1 B2)
    (width : ℕ) (input : List Bool) (L B : ℕ) (a : DS VV MM)
    (hc : Cst a) (ha : EntryNumericData r a) (hkin : a.kin = [])
    (hW : 2 ≤ width)
    (hprep : (Program.prepWord B1 B2 r.call r.witness).length < 2 ^ width)
    (hleft : natBitLength (entryPosition r).1.val + 2 < 2 ^ width)
    (hright : natBitLength (entryPosition r).2.val + 2 < 2 ^ width)
    (hL : 1 + (structuralWord (entryStructuralRequest r)).length ≤ L)
    (hB : (entryCallee B1 B2).bud (.inl (entryStructuralRequest r)) ≤ B) :
    Hs (entryContext B1 B2 width input L B) structuralStep a
      (a.rc compactStore + 8 * (Program.prepWord B1 B2 r.call r.witness).length +
        40 * natBitLength (entryPosition r).1.val + 40 * natBitLength (entryPosition r).2.val + L + B + 110)
      (fun b => b.env structuralFlag = (structuralBit (entryStructuralRequest r)).toNat ∧
        b.kin = [] ∧ b.kout = structuralOutput (entryStructuralRequest r) ∧ b.kc = 3 ∧
        b.ip = a.ip ∧ b.out = a.out ∧ b.ram = a.ram ∧ Cst b ∧
        EntryNumericData r b ∧ Fr a b entryEvaluationScratch) := by
  let C := entryContext B1 B2 width input L B
  unfold structuralStep
  refine (Hs.seq (t2 := (1 + L + B) + 5 + 1)
    (emitStructuralInput_run C r a hc ha hkin hW hprep hleft hright hL) ?_).mono
      (by omega) (fun _ h => h)
  rintro b ⟨hbkin, hbi, hbo, hbm, hbko, _hbkc, hbc, hbfr, hbdata⟩
  have hin : b.kin = C.K.inw (.inl (entryStructuralRequest r)) := hbkin
  have hcall : Hs C (.op .kcall) b (1 + L + B)
      (fun d => d = b.called (structuralOutput (entryStructuralRequest r))) :=
    Hs.op (OpEx.kcall (C := C) (.inl (entryStructuralRequest r)) b hin hB) rfl
  refine Hs.seq (t1 := 1 + L + B) (t2 := 5) hcall ?_
  rintro d rfl
  let d := b.called (structuralOutput (entryStructuralRequest r))
  have hdc : Cst d := ⟨hbc.z, hbc.one, hbc.two⟩
  refine (readBitReply_run C structuralFlag (by decide)
    (structuralBit (entryStructuralRequest r)) d hdc rfl rfl).mono le_rfl ?_
  rintro e ⟨hev, hekc, herest, hec, hefr⟩
  rcases (by simpa only [Prod.mk.injEq] using herest) with ⟨hei, heo, hem, _herc, hek, heko⟩
  have hef : Fr a e entryEvaluationScratch :=
    (hbfr.weaken (fun _ hx => List.mem_append_left _ (List.mem_append_left _ hx))).trans
      (hefr.weaken (by decide))
  have herm : e.ram = a.ram := hem.trans hbm
  exact ⟨hev, hek, heko, hekc, hei.trans hbi, heo.trans hbo, herm, hec,
    ha.of_evaluation (congrFun herm _) (congrFun herm _) (congrFun herm _) hef, hef⟩

end NearQuarticWires.StageMainMask
