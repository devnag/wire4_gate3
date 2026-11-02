import Proof.Quartic.StageMainMask.ReplyFrameLoop
import Proof.Quartic.StageLift.MemorySource

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open StageLift

/-- `def:mask` and Step 4 of `sec:algorithm`, paper/paper.tex: the actual population reply is
retained in a separate binary record store before its value is read. -/
def populationReplyStore : Fin MM := 8

/-- `def:mask`, paper/paper.tex: the selected
original mixed-residual population occupies this actual scalar. -/
def populationValue : Fin VV := 43

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
consume the entire actual framed population answer, rewind its retained
bits and execute the ordinary binary natural-number decoder. -/
def readPopulationReply : St VV MM :=
  .seq (readReplyFrame populationReplyStore)
    (.seq (.op (.rwM populationReplyStore))
      (.seq (readMemoryNatural populationReplyStore) (.op (.copy populationValue t3))))

/-- `prop:time`, paper/paper.tex: the framed
population answer uses only the native binary-decoder variables and
the actual output scalar. -/
def populationReplyScratch : List (Fin VV) := rdNatT ++ [populationValue]

/-- `def:mask`, Step 4 of `sec:algorithm` and `prop:time`,
paper/paper.tex:
every reply marker, retained bit and binary arithmetic read is paid,
and the decoded population is the actual subroutine's natural value. -/
theorem readPopulationReply_run (C : Ctx) (value : ℕ) (a : DS VV MM)
    (hc : Cst a) (ho : a.kout = frame (natWord value)) (hk : a.kc = 0)
    (hempty : a.ram populationReplyStore = []) (hcursor : a.rc populationReplyStore = 0)
    (hW : natBitLength value + 2 ≤ C.Wd) :
    Hs C readPopulationReply a (9 * (natWord value).length + 30 * natBitLength value + 40)
      (fun b => b.env populationValue = value ∧ b.kc = (frame (natWord value)).length ∧
        b.ip = a.ip ∧ b.out = a.out ∧ b.kin = a.kin ∧ b.kout = a.kout ∧
        (∀ other, other ≠ populationReplyStore → b.ram other = a.ram other) ∧
        Cst b ∧ Fr a b populationReplyScratch) := by
  unfold readPopulationReply
  refine (Hs.seq (t1 := 8 * (natWord value).length + 4)
    (t2 := ((natWord value).length + 1) + (30 * natBitLength value + 30 + 1 + 1) + 1)
    (readReplyFrame_spec C populationReplyStore (natWord value) [] a hc
      (by rw [ho, hk, List.drop_zero, List.append_nil]) (by rw [hcursor, hempty]; rfl)) ?_).mono
        (by omega) (fun _ h => h)
  rintro b ⟨hbk, hbr, hbrc, hbother, hbrest, hbc, hbfr⟩
  have hbr' : b.ram populationReplyStore = (natWord value).map Bool.toNat := by
    simpa only [hempty, List.nil_append] using hbr
  have hbrc' : b.rc populationReplyStore = (natWord value).length := by omega
  refine Hs.seq (t1 := (natWord value).length + 1)
    (t2 := 30 * natBitLength value + 30 + 1 + 1)
    ((hs_rwM C populationReplyStore b).mono (by rw [hbrc']) (fun _ h => h)) ?_
  rintro d rfl
  let d := b.rew populationReplyStore
  have hdc : Cst d := ⟨hbc.z, hbc.one, hbc.two⟩
  refine Hs.seq (t1 := 30 * natBitLength value + 30) (t2 := 1)
    (readMemoryNatural_spec C populationReplyStore (natWord value) d hdc hbr' value []
      (by simp [d, DS.rew]) hW) ?_
  rintro e ⟨hev, _hel, _herc, herest, hefr⟩
  have hem : e.ram = d.ram := congrArg (fun t => t.2.2.1) herest
  have hei : e.ip = d.ip := congrArg (fun t => t.1) herest
  have heo : e.out = d.out := congrArg (fun t => t.2.1) herest
  have hek : e.kin = d.kin := congrArg (fun t => t.2.2.2.2.1) herest
  have heko : e.kout = d.kout := congrArg (fun t => t.2.2.2.2.2.1) herest
  have hekc : e.kc = d.kc := congrArg (fun t => t.2.2.2.2.2.2) herest
  have hec := Cst.of_fr hdc hefr (by decide)
  refine (hs_copy C populationValue t3 e (by decide)).mono le_rfl ?_
  rintro f rfl
  have hff : Fr e (e.set populationValue (e.env t3)) populationReplyScratch :=
    Fr.set e _ (by simp [populationReplyScratch])
  rcases (by simpa only [Prod.mk.injEq] using hbrest) with ⟨hbi, hbo, hbki, hbko⟩
  refine ⟨hev, ?_, hei.trans hbi, heo.trans hbo, hek.trans hbki, heko.trans hbko,
    ?_, Cst.of_fr hec hff (by decide), ?_⟩
  · change e.kc = _
    rw [hekc]
    exact hbk.trans (by rw [hk]; omega)
  · intro other hother
    change e.ram other = _
    rw [hem]
    exact (hbother other hother).1
  · exact (hbfr.weaken (by decide)).trans
      ((hefr.weaken (fun _ hx => List.mem_append_left _ hx)).trans hff)

end NearQuarticWires.StageMainMask
