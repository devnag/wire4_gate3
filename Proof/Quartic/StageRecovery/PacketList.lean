import Proof.Quartic.StageRecovery.PacketEntry
import Proof.Gates.WordPrograms.RecLoop

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open NearCubicGates.Close.WordPrograms (recStream)

/-- `lem:print`, paper/paper.tex: the native table entry
count, retained independently of record-reader scratch variables. -/
def countVar : Fin VV := ⟨67, by decide⟩

/-- `lem:print`, paper/paper.tex: the actual framed native
records of a nonnegative signed table, in their existing table order. -/
def packetStream (width : ℕ) (values : List ℕ) : List Bool :=
  recStream (values.map fun value => binary width (2 * value))

/-- `lem:print`, paper/paper.tex: record offsets are the
exact paid fixed-width physical offsets, including each frame marker. -/
theorem packetStream_drop_head (width : ℕ) (values : List ℕ)
    (k : ℕ) (hk : k < values.length) :
    (packetStream width values).drop (k * (2 * width + 1)) =
      frame (binary width (2 * values[k])) ++ packetStream width (values.drop (k + 1)) := by
  have hs : values = values.take k ++ values[k] :: values.drop (k + 1) := by simp
  have hlen : (((values.take k).map (fun value => binary width (2 * value))).flatMap frame).length =
      k * (2 * width + 1) := by
    rw [NearCubicGates.Close.WordPrograms.flatMap_frame_length width _
      (by intro w hw; obtain ⟨v, _, rfl⟩ := List.mem_map.mp hw; simp)]
    simp only [List.length_map, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
  unfold packetStream
  conv_lhs => rw [hs]
  simp only [recStream, List.map_append, List.map_cons, List.flatMap_append, List.flatMap_cons]
  rw [← hlen]
  simp only [List.append_assoc, List.drop_left]

/-- `lem:print`, paper/paper.tex: the complete native
table is decoded by one sequential record loop. -/
def packetList : St VV MM := forS c0 countVar packetEntry

/-- `lem:print`, paper/paper.tex, and `prop:time`:1849–1853:
all native entries are centered and serialized in the same order in a
linear number of bounded-width per-entry operations. -/
theorem packetList_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (width q : ℕ) (values : List ℕ) (cost : ℕ)
    (hin : C.inp.drop a.ip = packetStream width values)
    (hcount : a.env countVar = values.length) (hcountfit : values.length < 2 ^ C.Wd)
    (hvalues : ∀ value ∈ values, 2 * value < 2 ^ width)
    (hwidth : width + 2 ≤ C.Wd) (hq : 0 < q) (haq : a.env modulusVar = q)
    (hqfit : 2 * q ≤ 2 ^ C.Wd) (hW : 1 < 2 ^ C.Wd)
    (hsfit : ∀ value ∈ values, natBitLength (naturalSign q value) + 2 < 2 ^ C.Wd)
    (hmfit : ∀ value ∈ values, natBitLength (naturalMagnitude q value) + 2 < 2 ^ C.Wd)
    (hcost : ∀ value ∈ values, packetEntryCost width q value ≤ cost) :
    Hs C packetList a (values.length * (cost + 4) + 4) (fun b =>
      b.out = a.out ++ values.flatMap (fun value : ℕ => intWord (Walks.centeredResidue q value)) ∧
      b.ip = a.ip + values.length * (2 * width + 1) ∧ Cst b) := by
  let I : ℕ → DS VV MM → Prop := fun k b => Cst b ∧ b.env modulusVar = q ∧
    b.ip = a.ip + k * (2 * width + 1) ∧
    b.out = a.out ++ (values.take k).flatMap (fun value : ℕ => intWord (Walks.centeredResidue q value))
  unfold packetList
  refine (forS_spec' c0 countVar (by decide) packetEntry a values.length hcountfit I cost
    (fun k b v ⟨hbc, hbq, hbi, hbo⟩ => ?_)
    ⟨hc, haq, by simp, by simp⟩ hcount ?_).mono le_rfl ?_
  · exact ⟨Cst.of_fr (T := [c0]) hbc (Fr.set _ _ (by decide)) (by decide),
      by simpa (config := {decide := true}) [DS.set] using hbq, hbi, hbo⟩
  · intro k hk b ⟨hbc, hbq, hbi, hbo⟩ hbctr hbn
    have hmem : values[k] ∈ values := List.getElem_mem hk
    have hinput : C.inp.drop b.ip = frame (binary width (2 * values[k])) ++
        packetStream width (values.drop (k + 1)) := by
      rw [hbi, ← List.drop_drop, hin, packetStream_drop_head width values k hk]
    refine (packetEntry_spec C b hbc width q values[k] _ hinput
      (hvalues _ hmem) hwidth hq hbq hqfit hW (hsfit _ hmem) (hmfit _ hmem)).mono
        (hcost _ hmem) ?_
    rintro d ⟨hdo, hdi, hdq, hdc, hdf⟩
    refine ⟨⟨hdc, hdq, by rw [hdi, hbi]; ring, ?_⟩,
      by rw [hdf _ (by decide), hbctr], by rw [hdf _ (by decide), hbn]⟩
    rw [hdo, hbo, List.take_succ_eq_append_getElem hk, List.flatMap_append,
      List.flatMap_singleton, List.append_assoc]
  · rintro b ⟨⟨hbc, _, hbi, hbo⟩, _, _⟩
    exact ⟨by simpa using hbo, hbi, hbc⟩

end NearQuarticWires.StageRecovery
