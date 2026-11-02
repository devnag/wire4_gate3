import Proof.Quartic.StageCertTests.SignedEntry
import Proof.Gates.WordPrograms.RecLoop

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertTests

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open NearCubicGates.Close.WordPrograms (recStream)
open NearCubicGates.Close.WordPrograms.SInt (encS)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open StageRecovery (countVar)

/-- `lem:print`, paper/paper.tex:
the signed native packet retains its original fixed-width record order. -/
def signedStream (width : ℕ) (values : List ℤ) : List Bool :=
  recStream (values.map fun z => binary width (encS z))

/-- `lem:print`, paper/paper.tex:
the next native record begins at its exact paid fixed-width offset. -/
theorem signedStream_drop_head (width : ℕ) (values : List ℤ)
    (k : ℕ) (hk : k < values.length) :
    (signedStream width values).drop (k * (2 * width + 1)) =
      frame (binary width (encS values[k])) ++ signedStream width (values.drop (k+1)) := by
  have hs : values = values.take k ++ values[k] :: values.drop (k+1) := by simp
  have hlen : (((values.take k).map (fun z => binary width (encS z))).flatMap frame).length =
      k * (2 * width + 1) := by
    rw [NearCubicGates.Close.WordPrograms.flatMap_frame_length width _
      (by intro w hw; obtain ⟨z,_,rfl⟩ := List.mem_map.mp hw; simp)]
    simp only [List.length_map,List.length_take,Nat.min_eq_left (Nat.le_of_lt hk)]
  unfold signedStream
  conv_lhs => rw [hs]
  simp only [recStream,List.map_append,List.map_cons,List.flatMap_append,List.flatMap_cons]
  rw [←hlen]
  simp only [List.append_assoc,List.drop_left]

/-- `lem:print`, paper/paper.tex:
one sequential record loop converts the complete signed native packet. -/
def signedList : St VV MM := forS c0 countVar signedEntry

/-- `lem:print` and `prop:time`, paper/paper.tex: signed conversion costs linearly many
bounded-width entry operations, including arbitrary negative moments. -/
theorem signedList_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (width : ℕ) (values : List ℤ) (cost : ℕ)
    (hin : C.inp.drop a.ip = signedStream width values)
    (hcount : a.env countVar = values.length) (hcountfit : values.length < 2 ^ C.Wd)
    (hvalues : ∀ z ∈ values, encS z < 2 ^ width)
    (hwidth : width + 2 ≤ C.Wd) (hfour : 4 ≤ 2 ^ C.Wd)
    (hsfit : ∀ z ∈ values, natBitLength (if z < 0 then 1 else 0) + 2 < 2 ^ C.Wd)
    (hmfit : ∀ z ∈ values, natBitLength z.natAbs + 2 < 2 ^ C.Wd)
    (hcost : ∀ z ∈ values, signedEntryCost width z ≤ cost) :
    Hs C signedList a (values.length * (cost+4)+4) (fun b =>
      b.out = a.out ++ values.flatMap intWord ∧
      b.ip = a.ip + values.length * (2 * width + 1) ∧ Cst b) := by
  let I : ℕ → DS VV MM → Prop := fun k b => Cst b ∧
    b.ip = a.ip + k * (2 * width + 1) ∧ b.out = a.out ++ (values.take k).flatMap intWord
  unfold signedList
  refine (forS_spec' c0 countVar (by decide) signedEntry a values.length hcountfit I cost
    (fun k b v ⟨hbc,hbi,hbo⟩ => ?_)
    ⟨hc,by simp,by simp⟩ hcount ?_).mono le_rfl ?_
  · exact ⟨Cst.of_fr (T := [c0]) hbc (Fr.set _ _ (by decide)) (by decide),hbi,hbo⟩
  · intro k hk b ⟨hbc,hbi,hbo⟩ hbctr hbn
    have hmem : values[k] ∈ values := List.getElem_mem hk
    have hinput : C.inp.drop b.ip = frame (binary width (encS values[k])) ++
        signedStream width (values.drop (k+1)) := by
      rw [hbi,←List.drop_drop,hin,signedStream_drop_head width values k hk]
    refine (signedEntry_spec C b hbc width values[k] _ hinput
      (hvalues _ hmem) hwidth hfour (hsfit _ hmem) (hmfit _ hmem)).mono (hcost _ hmem) ?_
    rintro d ⟨hdo,hdi,hdc,hdf⟩
    refine ⟨⟨hdc,by rw [hdi,hbi];ring,?_⟩,
      by rw [hdf _ (by decide),hbctr],by rw [hdf _ (by decide),hbn]⟩
    rw [hdo,hbo,List.take_succ_eq_append_getElem hk,List.flatMap_append,
      List.flatMap_singleton,List.append_assoc]
  · rintro b ⟨⟨hbc,hbi,hbo⟩,_,_⟩
    exact ⟨by simpa using hbo,hbi,hbc⟩

end NearQuarticWires.StageCertTests
