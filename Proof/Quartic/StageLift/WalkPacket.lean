import Proof.Quartic.StageLift.WalkHeader
import Proof.Quartic.StageLift.WalkFrame

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: the actual
four scalar fields precede the physically framed complete original
walk source, in the one unchanged raw packet codec. -/
def emitWalkPacket : St VV MM := .seq emitRawWalkHeader emitFramedWalkPayload

/-- `lem:print` and Step 3, paper/paper.tex: one actual walk emits exactly its shared five-field packet,
advances the real Gamma source once and retains the source invariant. -/
theorem emitWalkPacket_spec {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (index : Fin (r.child.cellCall.seed.N ^ 8)) (a : DS VV MM)
    (ha : WalkSourceState (printSourceContext B1 B2 (Greedy.printInput r)) r index.val a)
    (hi : a.env printWalkIndex = index.val) :
    let C := printSourceContext B1 B2 (Greedy.printInput r)
    Hs C emitWalkPacket a (walkPacketCost r C.Lk C.Bk) (fun z =>
      z.out = a.out ++ (sourceWalkPacket r index).word ∧
      WalkSourceState C r (index.val + 1) z ∧ z.env printWalkIndex = index.val ∧ z.ip = a.ip) := by
  dsimp only
  let C := printSourceContext B1 B2 (Greedy.printInput r)
  have hW : 100 * (sourceEnvelope r + 1) ^ 2 ≤ C.Wd := by
    change _ ≤ (printSourceSizes B1 B2).W (leadOnes (Greedy.printInput r))
    simpa only [List.append_nil] using printSourceSizes_width r []
  unfold emitWalkPacket
  refine (Hs.seq (t1 := 1600 * (sourceEnvelope r + 1) ^ 2 + 173)
    (t2 := 3 * walkPayloadCost r C.Lk C.Bk + 2)
    (emitSelectedWalkHeader_spec C r index a ha hi hW)
    fun b ⟨hbo,hbstate,hbI,hbip⟩ => ?_).mono ?_ (fun _ h => h)
  · refine (emitFramedWalkPayload_spec r index b hbstate hbI).mono le_rfl ?_
    rintro z ⟨hzo,hzstate,hzI,hzip⟩
    refine ⟨?_,hzstate,hzI,hzip.trans hbip⟩
    rw [hzo,hbo]
    simp only [sourceWalkPacket,StageFormulaMetadata.RawWalkPacket.word,List.append_assoc]
  · change (1600 * (sourceEnvelope r + 1) ^ 2 + 173) +
        (3 * walkPayloadCost r C.Lk C.Bk + 2) + 1 ≤
      1600 * (sourceEnvelope r + 1) ^ 2 + 3 * walkPayloadCost r C.Lk C.Bk + 176
    omega

end NearQuarticWires.StageLift
