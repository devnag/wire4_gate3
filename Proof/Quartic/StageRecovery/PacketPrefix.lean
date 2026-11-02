import Proof.Quartic.StageRecovery.PacketMachine

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

/-- `lem:print`, paper/paper.tex: the same sequential
native record decoder can emit precisely the requested original-column
prefix while retaining padded trailing records as paid input. -/
theorem packetList_prefix_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (width q : ℕ) (values : List ℕ) (N cost : ℕ) (hN : N ≤ values.length)
    (hin : C.inp.drop a.ip = packetStream width values)
    (hcount : a.env countVar = N) (hcountfit : N < 2 ^ C.Wd)
    (hvalues : ∀ value ∈ values, 2 * value < 2 ^ width)
    (hwidth : width + 2 ≤ C.Wd) (hq : 0 < q) (haq : a.env modulusVar = q)
    (hqfit : 2 * q ≤ 2 ^ C.Wd) (hW : 1 < 2 ^ C.Wd)
    (hsfit : ∀ value ∈ values, natBitLength (naturalSign q value) + 2 < 2 ^ C.Wd)
    (hmfit : ∀ value ∈ values, natBitLength (naturalMagnitude q value) + 2 < 2 ^ C.Wd)
    (hcost : ∀ value ∈ values, packetEntryCost width q value ≤ cost) :
    Hs C packetList a (N * (cost + 4) + 4) (fun b =>
      b.out = a.out ++ (values.take N).flatMap (fun value : ℕ => intWord (Walks.centeredResidue q value)) ∧
      b.ip = a.ip + N * (2 * width + 1) ∧ Cst b) := by
  let I : ℕ → DS VV MM → Prop := fun k b => Cst b ∧ b.env modulusVar = q ∧
    b.ip = a.ip + k * (2 * width + 1) ∧
    b.out = a.out ++ (values.take k).flatMap (fun value : ℕ => intWord (Walks.centeredResidue q value))
  unfold packetList
  refine (forS_spec' c0 countVar (by decide) packetEntry a N hcountfit I cost
    (fun k b v ⟨hbc, hbq, hbi, hbo⟩ => ?_)
    ⟨hc, haq, by simp, by simp⟩ hcount ?_).mono le_rfl ?_
  · exact ⟨Cst.of_fr (T := [c0]) hbc (Fr.set _ _ (by decide)) (by decide),
      by simpa (config := {decide := true}) [DS.set] using hbq, hbi, hbo⟩
  · intro k hk b ⟨hbc, hbq, hbi, hbo⟩ hbctr hbn
    have hk' : k < values.length := hk.trans_le hN
    have hmem : values[k] ∈ values := List.getElem_mem hk'
    have hinput : C.inp.drop b.ip = frame (binary width (2 * values[k])) ++
        packetStream width (values.drop (k + 1)) := by
      rw [hbi, ← List.drop_drop, hin, packetStream_drop_head width values k hk']
    refine (packetEntry_spec C b hbc width q values[k] _ hinput
      (hvalues _ hmem) hwidth hq hbq hqfit hW (hsfit _ hmem) (hmfit _ hmem)).mono
        (hcost _ hmem) ?_
    rintro d ⟨hdo, hdi, hdq, hdc, hdf⟩
    refine ⟨⟨hdc, hdq, by rw [hdi, hbi]; ring, ?_⟩,
      by rw [hdf _ (by decide), hbctr], by rw [hdf _ (by decide), hbn]⟩
    rw [hdo, hbo, List.take_succ_eq_append_getElem hk', List.flatMap_append,
      List.flatMap_singleton, List.append_assoc]
  · rintro b ⟨⟨hbc, _, hbi, hbo⟩, _, _⟩
    exact ⟨hbo, hbi, hbc⟩

/-- `lem:print`, paper/paper.tex: an actual padded
native packet carries an original-column count bounded by its native
count; the existing decoder program itself is unchanged. -/
structure PacketPrefixRequest where
  native : PacketRequest
  count : ℕ
  count_le : count ≤ native.values.length

/-- `lem:print`, paper/paper.tex: the existing
three-field packet header contains the actual target prefix count,
followed by the complete unchanged native record packet. -/
def PacketPrefixRequest.word (r : PacketPrefixRequest) : List Bool :=
  RepairRepresentation.natWord r.native.hint ++ RepairRepresentation.natWord r.native.modulus ++
    RepairRepresentation.natWord r.count ++ packetStream r.native.width r.native.values

/-- `lem:print`, paper/paper.tex: canonical prefix
output retains precisely the requested original-column ordering. -/
def PacketPrefixRequest.output (r : PacketPrefixRequest) : List Bool :=
  listWord intWord ((r.native.values.take r.count).map fun value : ℕ =>
    Walks.centeredResidue r.native.modulus value)

end NearQuarticWires.StageRecovery
