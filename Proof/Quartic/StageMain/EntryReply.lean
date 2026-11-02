import Proof.Quartic.StageMain.Totals
import Proof.Quartic.StageMain.SampleReply

/-!
# The two Boolean answers of one sampled entry

Step 4 of `sec:algorithm`, paper/paper.tex:
the main controller reads both predicate and mask bits, including
all markers and the final delimiter of their actual framed reply.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Controller

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open SampleCells StageGamma

def readEntryReply : St VV MM :=
  .seq (.op (.rdK t0)) (.seq (.op (.rdK predicateFlag))
    (.seq (.op (.rdK t0)) (.seq (.op (.rdK maskFlag)) (.op (.rdK t0)))))

def entryReplyScratch : List (Fin VV) := [predicateFlag, maskFlag, t0]

theorem readEntryReply_run (C : Ctx) (pred mask : Bool) (a : DS VV MM)
    (hc : Cst a) (ho : a.kout = frame [pred, mask]) (hk : a.kc = 0) :
    Hs C readEntryReply a 9 (fun b =>
      b.env predicateFlag = pred.toNat ∧ b.env maskFlag = mask.toNat ∧
      b.kc = 5 ∧ ReplyFrame a b ∧ Cst b ∧ Fr a b entryReplyScratch) := by
  have hlen : a.kout.length = 5 := by rw [ho, frame_length]; rfl
  unfold readEntryReply
  refine Hs.seq (t1 := 1) (t2 := 7) (hs_rdK C t0 a (by omega)) ?_
  rintro b rfl
  refine Hs.seq (t1 := 1) (t2 := 5) (hs_rdK C predicateFlag _ (by
    change a.kc + 1 < a.kout.length; omega)) ?_
  rintro d rfl
  refine Hs.seq (t1 := 1) (t2 := 3) (hs_rdK C t0 _ (by
    change a.kc + 1 + 1 < a.kout.length; omega)) ?_
  rintro e rfl
  refine Hs.seq (t1 := 1) (t2 := 1) (hs_rdK C maskFlag _ (by
    change a.kc + 1 + 1 + 1 < a.kout.length; omega)) ?_
  rintro f rfl
  refine (hs_rdK C t0 _ (by
    change a.kc + 1 + 1 + 1 + 1 < a.kout.length; omega)).mono le_rfl ?_
  rintro g rfl
  let z := ((((a.set t0 (bitOf a.kout a.kc)).set predicateFlag
    (bitOf a.kout (a.kc + 1))).set t0 (bitOf a.kout (a.kc + 1 + 1))).set maskFlag
    (bitOf a.kout (a.kc + 1 + 1 + 1))).set t0 (bitOf a.kout (a.kc + 1 + 1 + 1 + 1))
  have hf : Fr a z entryReplyScratch :=
    (Fr.set a _ (by simp [entryReplyScratch])).trans
      ((Fr.set _ _ (by simp [entryReplyScratch])).trans
        ((Fr.set _ _ (by simp [entryReplyScratch])).trans
          ((Fr.set _ _ (by simp [entryReplyScratch])).trans
            (Fr.set _ _ (by simp [entryReplyScratch])))))
  exact ⟨by simp (config := {decide := true}) [DS.set, ho, hk, bitOf, frame, predicateFlag, maskFlag, t0],
    by simp (config := {decide := true}) [DS.set, ho, hk, bitOf, frame, predicateFlag, maskFlag, t0],
    by change a.kc + 1 + 1 + 1 + 1 + 1 = 5; omega,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩,
    Cst.of_fr hc hf (by decide), hf⟩

end NearQuarticWires.StageMain.Controller
