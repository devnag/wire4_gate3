import Proof.Quartic.StageGamma.Unframe

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageGamma

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms

variable {ns nr : ℕ}

/-- `cor:conditional`, paper/paper.tex: a finite list
of destination tapes and their self-delimiting contents. -/
abbrev TapeRecords (ns : ℕ) := List (Fin (ns + 1) × List Bool)

/-- `cor:conditional`, paper/paper.tex: serialize the
actual cached modulus, conjunction and finite Gaussian workspaces. -/
def recordsWord (records : TapeRecords ns) : List Bool :=
  records.flatMap (fun record => frame record.2)

/-- `cor:conditional`, paper/paper.tex: a fixed
sequence of physical tape-record decoders. -/
def loadRecords (src : Fin (ns + 1)) (OP : Fin nr) : TapeRecords ns → WM ns nr
  | [] => .skip
  | record :: records => .seq (unframeRecord src record.1 OP) (loadRecords src OP records)

/-- `prop:time`, paper/paper.tex: loading is linear
in the actual number of serialized tape bits. -/
def loadRecordsCost : TapeRecords ns → ℕ
  | [] => 1
  | record :: records => 23 * record.2.length + 6 + loadRecordsCost records

/-- `cor:conditional`, paper/paper.tex: the resulting
tape state is explicitly determined by the decoded finite record list. -/
def loadedRecords (src : Fin (ns + 1)) (σ : WState ns nr) : TapeRecords ns → WState ns nr
  | [] => σ
  | record :: records =>
      loadedRecords src
        ((σ.sets record.1 record.2).seth src (σ.sh src + 2 * record.2.length + 1)) records

/-- `cor:conditional`, paper/paper.tex: the decoder's
finite control depends only on the fixed destination slots. -/
def loadTapeSlots (src : Fin (ns + 1)) (OP : Fin nr) : List (Fin (ns + 1)) → WM ns nr
  | [] => .skip
  | dst :: dests => .seq (unframeRecord src dst OP) (loadTapeSlots src OP dests)

/-- `cor:conditional`, paper/paper.tex: no record
contents are installed in the finite machine's description. -/
theorem loadRecords_eq_slots (src : Fin (ns + 1)) (OP : Fin nr) (records : TapeRecords ns) :
    loadRecords src OP records = loadTapeSlots src OP (records.map Prod.fst) := by
  induction records with
  | nil => rfl
  | cons r rs ih => simp only [loadRecords, List.map_cons, loadTapeSlots, ih]

/-- `cor:conditional`, paper/paper.tex: every
destination head stays at its original position after loading. -/
theorem loadedRecords_head (src dst : Fin (ns + 1)) (hne : dst ≠ src)
    (σ : WState ns nr) (records : TapeRecords ns) :
    (loadedRecords src σ records).sh dst = σ.sh dst := by
  induction records generalizing σ with
  | nil => rfl
  | cons r rs ih => simpa [loadedRecords, Function.update_of_ne hne] using
      (ih ((σ.sets r.1 r.2).seth src (σ.sh src + 2 * r.2.length + 1)))

/-- `cor:conditional`, paper/paper.tex: loading
preserves every tape outside its fixed destination list. -/
theorem loadedRecords_other (src dst : Fin (ns + 1)) (σ : WState ns nr)
    (records : TapeRecords ns) (h : dst ∉ records.map Prod.fst) :
    (loadedRecords src σ records).st dst = σ.st dst := by
  induction records generalizing σ with
  | nil => rfl
  | cons r rs ih =>
    have hh : dst ≠ r.1 ∧ dst ∉ rs.map Prod.fst := by simpa using h
    simpa [loadedRecords, Function.update_of_ne hh.1] using
      ih ((σ.sets r.1 r.2).seth src (σ.sh src + 2 * r.2.length + 1)) hh.2

/-- `cor:conditional`, paper/paper.tex: each decoded
record occupies exactly its specified physical destination tape. -/
theorem loadedRecords_mem (src : Fin (ns + 1)) (σ : WState ns nr)
    (records : TapeRecords ns) (hn : (records.map Prod.fst).Nodup)
    (r : Fin (ns + 1) × List Bool) (hr : r ∈ records) :
    (loadedRecords src σ records).st r.1 = r.2 := by
  induction records generalizing σ with
  | nil => simp at hr
  | cons r0 rs ih =>
    have hnd : r0.1 ∉ rs.map Prod.fst ∧ (rs.map Prod.fst).Nodup := by simpa using hn
    rcases List.mem_cons.mp hr with rfl | hr
    · rw [loadedRecords, loadedRecords_other src r.1 _ rs hnd.1]
      simp
    · exact ih ((σ.sets r0.1 r0.2).seth src (σ.sh src + 2 * r0.2.length + 1)) hnd.2 hr

/-- `prop:time`, paper/paper.tex: the record loader's
transition count is bounded by its actual serialized input length. -/
theorem loadRecordsCost_le (records : TapeRecords ns) :
    loadRecordsCost records ≤ 23 * (recordsWord records).length + 1 := by
  induction records with
  | nil => simp [loadRecordsCost, recordsWord]
  | cons r rs ih =>
    simp only [loadRecordsCost, recordsWord, List.flatMap_cons, List.length_append, frame_length] at *
    omega

/-- `cor:conditional`, paper/paper.tex: all records
are loaded by an actual finite machine, with no preinstalled nonblank tape. -/
theorem loadRecords_run (cap : ℕ) (src : Fin (ns + 1)) (OP : Fin nr)
    (records : TapeRecords ns) (hn : (records.map Prod.fst).Nodup)
    (hsafe : ∀ record ∈ records, src ≠ record.1)
    (hcap : ∀ record ∈ records, record.2.length ≤ cap)
    (pre rest : List Bool) (σ : WState ns nr)
    (hst : σ.st src = pre ++ recordsWord records ++ rest)
    (hsh : σ.sh src = pre.length) (hOP : σ.val OP = 0)
    (hblank : ∀ record ∈ records, σ.st record.1 = [] ∧ σ.sh record.1 = 0) :
    WExec cap (loadRecords src OP records) σ (loadedRecords src σ records)
      (loadRecordsCost records) := by
  induction records generalizing pre σ with
  | nil => exact WExec.mono (WExec.skip σ) (by simp [loadRecordsCost])
  | cons record records ih =>
    have hnd : record.1 ∉ records.map Prod.fst ∧ (records.map Prod.fst).Nodup := by
      simpa using hn
    have hsd := hsafe record (by simp)
    have hrecord := hblank record (by simp)
    have h1 := unframeRecord_run cap src record.1 hsd OP record.2 pre
      (recordsWord records ++ rest) σ
      (by simpa [recordsWord, List.append_assoc] using hst) hsh
      (by rw [hrecord.1, hrecord.2]; rfl) hOP (hcap record (by simp))
    let σ1 := (σ.sets record.1 record.2).seth src (σ.sh src + 2 * record.2.length + 1)
    have h1' : WExec cap (unframeRecord src record.1 OP) σ σ1
        (23 * record.2.length + 5) := by
      simpa [σ1, hrecord.1, hsh] using h1
    have h2 := ih hnd.2 (fun r hr => hsafe r (by simp [hr]))
      (fun r hr => hcap r (by simp [hr])) (pre ++ frame record.2) σ1
      (by simp [σ1, Function.update_of_ne hsd, hst, recordsWord, List.append_assoc])
      (by simp [σ1, hsh, frame_length]; omega)
      (by simpa [σ1] using hOP) (by
        intro r hr
        have hne : r.1 ≠ record.1 := by
          intro heq
          exact hnd.1 (List.mem_map.mpr ⟨r, hr, heq⟩)
        have hsr := hsafe r (by simp [hr])
        have hrblank := hblank r (by simp [hr])
        simpa [σ1, Function.update_of_ne hne, Function.update_of_ne hsr.symm] using hrblank)
    simpa [loadRecords, loadedRecords, loadRecordsCost, σ1, Nat.add_assoc] using WExec.seq h1' h2

end NearQuarticWires.StageGamma
