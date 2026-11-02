import Proof.Quartic.StageRecovery.FamilyRecordLoad

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicGates.Close.Cells NearCubicGates.Close.WordPrograms

/-- `lem:print`, paper/paper.tex: the exact native
support packet consists of fixed binary records and its final delimiter. -/
def nativeFamilyPacket (W : ℕ) (records : List ℕ) : List Bool :=
  recStream (records.map (binary W))

/-- `lem:print`, paper/paper.tex: every native packet
has an actual last marker, including the empty-record case. -/
theorem nativeFamilyPacket_length (W : ℕ) (records : List ℕ) :
    (nativeFamilyPacket W records).length = records.length * (2 * W + 1) + 1 := by
  simp [nativeFamilyPacket, recStream, List.length_flatMap, frame_length,
    binary_length, Function.comp_def]

/-- `lem:print`, paper/paper.tex: a nonempty fixed-width
record starts with a true frame marker; the packet terminator is false. -/
theorem nativeFamilyPacket_head (W : ℕ) (records : List ℕ) (hW : 0 < W) :
    (nativeFamilyPacket W records).headD false = decide (records ≠ []) := by
  cases records with
  | nil => rfl
  | cons x records =>
      cases W with
      | zero => omega
      | succ W => rfl

/-- `lem:print`, paper/paper.tex: after one actual
record the remaining bytes are precisely the next native packet suffix. -/
theorem nativeFamilyPacket_cons (W x : ℕ) (records : List ℕ) :
    nativeFamilyPacket W (x :: records) = frame (binary W x) ++ nativeFamilyPacket W records := by
  simp [nativeFamilyPacket, recStream, List.append_assoc]

/-- `lem:print`, paper/paper.tex: native record offsets
are the paid sum of all preceding finite frame lengths. -/
theorem nativeFamilyPacket_offset (W : ℕ) (records : List ℕ) (k : ℕ) (hk : k ≤ records.length) :
    (nativeFamilyPacket W records).drop (k * (2 * W + 1)) = nativeFamilyPacket W (records.drop k) := by
  have he : nativeFamilyPacket W records =
      ((records.take k).flatMap fun x => frame (binary W x)) ++ nativeFamilyPacket W (records.drop k) := by
    calc nativeFamilyPacket W records = nativeFamilyPacket W (records.take k ++ records.drop k) :=
        congrArg (nativeFamilyPacket W) (List.take_append_drop k records).symm
      _ = _ := by
        simp only [nativeFamilyPacket, recStream, List.map_append, List.flatMap_append,
          List.flatMap_map, Function.comp_def, List.append_assoc]
  have hl : ((records.take k).flatMap fun x => frame (binary W x)).length = k * (2 * W + 1) := by
    simp [List.length_flatMap, frame_length, binary_length, List.length_take, min_eq_left hk]
  rw [he, ← hl, List.drop_left]

/-- `lem:print`, paper/paper.tex: a native marker is
read from the actual input tape; no output-length observation is used. -/
def readFamilyMarkerProgram : St VV MM := .op (.rdI t0)

/-- `lem:print`, paper/paper.tex: one physical marker
read distinguishes the next framed record from the native terminator,
retaining all stores, buffers and request metadata. -/
theorem readFamilyMarkerProgram_spec (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (W : ℕ) (records : List ℕ) (rest : List Bool) (hW : 0 < W)
    (hin : C.inp.drop a.ip = nativeFamilyPacket W records ++ rest) :
    Hs C readFamilyMarkerProgram a 1 (fun b =>
      b.env t0 = (decide (records ≠ [])).toNat ∧ b.ip = a.ip + 1 ∧
      (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) = (a.out, a.ram, a.rc, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b [t0]) := by
  have hp : 0 < (nativeFamilyPacket W records).length := by rw [nativeFamilyPacket_length]; omega
  have hbit : bitOf C.inp a.ip = (decide (records ≠ [])).toNat := by
    have hh := bitOf_drop hin 0 hp
    change bitOf C.inp a.ip = _
    have he : (nativeFamilyPacket W records).getD 0 false = (decide (records ≠ [])) := by
      cases records with
      | nil => rfl
      | cons x records => cases W with
        | zero => omega
        | succ W => rfl
    simpa only [Nat.add_zero, he] using hh
  refine (hs_rdI C t0 a (lt_of_drop hin 0 hp)).mono le_rfl ?_
  rintro b rfl
  have hf : Fr a ({ a.set t0 (bitOf C.inp a.ip) with ip := a.ip + 1 } : DS VV MM) [t0] := by
    intro y hy
    exact DS.set_env_ne _ _ (by simpa only [List.mem_singleton] using hy)
  exact ⟨by simpa only [DS.set_env_self] using hbit, rfl, rfl,
    Cst.of_fr hc hf (by decide), hf⟩

end NearQuarticWires.StageRecovery
