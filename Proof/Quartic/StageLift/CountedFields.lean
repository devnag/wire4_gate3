import Proof.Quartic.StageLift.Fields
import Proof.Gates.Cells.Loop

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells

/-- `sec:params` and `lem:print`, paper/paper.tex: a fixed loop index for counted prime and factor payloads. -/
def fieldIndex : Fin VV := ⟨120, by decide⟩

/-- `sec:params` and `lem:print`, paper/paper.tex: a payload's actual decoded length controls its parser. -/
def readCountedFields (store : Fin MM) (count : Fin VV) : St VV MM :=
  forS fieldIndex count (readFixedFields store 1)

/-- `sec:params` and `lem:print`, paper/paper.tex: counted list fields are decoded physically into the
retained store, with linear field-count and binary-width cost. -/
theorem readCountedFields_spec (C : Ctx) (store : Fin MM) (count : Fin VV)
    (hcount : count ∉ fieldIndex :: rdNatT) (values : List ℕ) (B : ℕ)
    (rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = values.flatMap natWord ++ rest)
    (hwidth : ∀ value ∈ values, natBitLength value ≤ B)
    (hB : B + 2 ≤ C.Wd) (hcountValue : a.env count = values.length)
    (hcountFit : values.length < 2 ^ C.Wd)
    (hcursor : a.rc store = (a.ram store).length) :
    Hs C (readCountedFields store count) a (values.length * (30 * B + 39) + 4) (fun b =>
      b.ip = a.ip + (values.flatMap natWord).length ∧
      b.ram store = a.ram store ++ values ∧ b.rc store = a.rc store + values.length ∧
      (∀ other, other ≠ store → b.ram other = a.ram other ∧ b.rc other = a.rc other) ∧
      (b.out, b.kin, b.kout, b.kc) = (a.out, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b (fieldIndex :: rdNatT)) := by
  have hne : fieldIndex ≠ count := by
    intro he
    exact hcount (by simp [← he])
  let I (k : ℕ) (b : DS VV MM) : Prop :=
    b.ip = a.ip + ((values.take k).flatMap natWord).length ∧
    b.ram store = a.ram store ++ values.take k ∧ b.rc store = a.rc store + k ∧
    (∀ other, other ≠ store → b.ram other = a.ram other ∧ b.rc other = a.rc other) ∧
    (b.out, b.kin, b.kout, b.kc) = (a.out, a.kin, a.kout, a.kc) ∧
    Cst b ∧ Fr a b (fieldIndex :: rdNatT)
  have hIi : ∀ k b v, I k b → I k (b.set fieldIndex v) := by
    intro k b v ⟨hi, hr, hrc, ho, hs, hbc, hf⟩
    exact ⟨hi, hr, hrc, ho, hs,
      Cst.of_fr (T := [fieldIndex]) hbc (Fr.set b v (by simp)) (by decide),
      hf.trans (Fr.set b v (by simp))⟩
  have h0 : I 0 a := by
    exact ⟨by simp, by simp, by simp, fun _ _ => ⟨rfl, rfl⟩, rfl, hc, Fr.refl _ _⟩
  refine (forS_spec' (C := C) fieldIndex count hne (readFixedFields store 1) a values.length
    hcountFit I (30 * B + 35) hIi h0 hcountValue ?_).mono le_rfl ?_
  · intro k hk b ⟨hbi, hbr, hbrc, hbother, hbsh, hbc, hbf⟩ hki hcn
    have hsplit : values.flatMap natWord =
        (values.take k).flatMap natWord ++ natWord values[k] ++
          (values.drop (k + 1)).flatMap natWord := by
      conv_lhs => rw [← List.take_append_drop k values]
      rw [List.flatMap_append, List.drop_eq_getElem_cons hk, List.flatMap_cons, List.append_assoc]
    have hbin : C.inp.drop b.ip = natWord values[k] ++
        ((values.drop (k + 1)).flatMap natWord ++ rest) := by
      rw [hbi, ← List.drop_drop, hin, hsplit, List.append_assoc, List.append_assoc,
        List.drop_left]
    have hbcursor : b.rc store = (b.ram store).length := by
      rw [hbr, List.length_append, List.length_take, min_eq_left hk.le, hbrc, hcursor]
    have he := readFixedFields_spec C store [values[k]]
      ((values.drop (k + 1)).flatMap natWord ++ rest) b hbc
      (by simpa using hbin) (by
        intro v hv
        simp only [List.mem_singleton] at hv
        subst v
        exact (Nat.add_le_add_right (hwidth values[k] (List.getElem_mem hk)) 2).trans hB)
      hbcursor
    refine he.mono (by simp; have := hwidth values[k] (List.getElem_mem hk); omega) ?_
    rintro d ⟨hdi, hdr, hdrc, hdother, hdsh, hdc, hdf⟩
    refine ⟨⟨?_, ?_, ?_, ?_, hdsh.trans hbsh, hdc,
      hbf.trans (hdf.weaken (by intro y hy; exact List.mem_cons_of_mem _ hy))⟩, ?_, ?_⟩
    · rw [hdi, hbi, List.take_succ_eq_append_getElem hk, List.flatMap_append,
        List.flatMap_singleton, List.length_append]
      omega
    · rw [hdr, hbr, List.take_succ_eq_append_getElem hk]
      simp [List.append_assoc]
    · rw [hdrc, hbrc]
      simp
      omega
    · intro other hother
      obtain ⟨hdr', hdc'⟩ := hdother other hother
      obtain ⟨hbr', hbc'⟩ := hbother other hother
      exact ⟨hdr'.trans hbr', hdc'.trans hbc'⟩
    · rw [hdf fieldIndex (by decide)]
      exact hki
    · rw [hdf count (by intro h; exact hcount (List.mem_cons_of_mem _ h))]
      exact hcn
  · rintro b ⟨hb, _, _⟩
    simpa only [I, List.take_length] using hb

end NearQuarticWires.StageLift
