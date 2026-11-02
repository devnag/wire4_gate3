import Proof.Quartic.StageLift.WalkPacket

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicGates.Close.Cells

/-- Step 3 and `lem:print`, paper/paper.tex: the actual Gamma header supplies the complete original
walk loop; zero weights and every original occurrence are retained. -/
def emitAllWalkPackets : St VV MM := forS printWalkIndex printWalkCount emitWalkPacket

/-- Step 3, `lem:print` and `prop:time`, paper/paper.tex: the physical all-walk loop
emits every exact original packet in its low-first order, with actual
counter tests, increments, source queries and Gamma cursor movement. -/
theorem emitAllWalkPackets_spec {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (a : DS VV MM) (ha : CarrierStartData r a) (hc : Cst a)
    (hv : Valid (printSourceContext B1 B2 (Greedy.printInput r)) a) (hkin : a.kin = []) :
    let C := printSourceContext B1 B2 (Greedy.printInput r)
    Hs C emitAllWalkPackets a (allWalkSourceCost r C.Lk C.Bk) (fun z =>
      z.out = a.out ++ sourcePacketPrefix r (r.child.cellCall.seed.N ^ 8) ∧
      WalkSourceState C r (r.child.cellCall.seed.N ^ 8) z ∧
      z.env printWalkIndex = r.child.cellCall.seed.N ^ 8 ∧
      z.env printWalkCount = r.child.cellCall.seed.N ^ 8 ∧ z.ip = a.ip) := by
  dsimp only
  let C := printSourceContext B1 B2 (Greedy.printInput r)
  have hW : 100 * (sourceEnvelope r + 1) ^ 2 ≤ C.Wd := by
    change _ ≤ (printSourceSizes B1 B2).W (leadOnes (Greedy.printInput r))
    simpa only [List.append_nil] using printSourceSizes_width r []
  have hsmall : sourceEnvelope r + 1 ≤ (sourceEnvelope r + 1) ^ 2 := Nat.le_self_pow (by decide) _
  have hbits := source_walk_counter_bits r
  have hfit : r.child.cellCall.seed.N ^ 8 < 2 ^ C.Wd :=
    (lt_natBitLength _).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  let I : ℕ → DS VV MM → Prop := fun k b =>
    b.out = a.out ++ sourcePacketPrefix r k ∧ WalkSourceState C r k b ∧ b.ip = a.ip
  have hIi : ∀ k b value, I k b → I k (b.set printWalkIndex value) := by
    intro k b value ⟨hbo,hbs,hbi⟩
    exact ⟨hbo,hbs.setCounter value,hbi⟩
  have hzero : I 0 a := by
    refine ⟨?_,WalkSourceState.of_start ha hc hv hkin,rfl⟩
    simp only [sourcePacketPrefix,List.take_zero,List.flatMap_nil,List.append_nil]
  unfold emitAllWalkPackets
  refine (forS_spec' (C := C) printWalkIndex printWalkCount (by decide) emitWalkPacket
    a (r.child.cellCall.seed.N ^ 8) hfit I (walkPacketCost r C.Lk C.Bk) hIi hzero ha.walkCount
    ?_).mono ?_ ?_
  · intro k hk b ⟨hbo,hbstate,hbip⟩ hindex _hcount
    refine (emitWalkPacket_spec r ⟨k,hk⟩ b hbstate hindex).mono le_rfl ?_
    rintro z ⟨hzo,hzstate,hzI,hzip⟩
    refine ⟨⟨?_,hzstate,hzip.trans hbip⟩,hzI,hzstate.sources.walkCount⟩
    rw [hzo,hbo,sourcePacketPrefix_succ r k hk,List.append_assoc]
  · change (r.child.cellCall.seed.N ^ 8) * (walkPacketCost r C.Lk C.Bk + 4) + 4 ≤
      (r.child.cellCall.seed.N ^ 8) * (walkPacketCost r C.Lk C.Bk + 4) + 4
    exact le_rfl
  · rintro z ⟨⟨hzo,hzstate,hzip⟩,hzI,hzN⟩
    exact ⟨hzo,hzstate,hzI,hzN,hzip⟩

end NearQuarticWires.StageLift
