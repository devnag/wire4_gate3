import Proof.Quartic.StageLift.IndexInteger
import Proof.Quartic.StageLift.CountedFields

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open NearQuarticWires.StageRecovery

/-- `lem:print`, paper/paper.tex: a genuine
decoded list count controls one pass over the original signed index
fields; only their actual reduced residues are retained. -/
def readIndexPayload (markers target : Fin MM) (count : Fin VV) : St VV MM :=
  forS fieldIndex count (readIndexInteger markers target)

/-- `lem:print`, paper/paper.tex: arbitrary raw
integer fields are normalized once into a bounded bank. B bounds their
input bit lengths only for the additive cost estimate; B is not a
register or an arithmetic-width assumption. -/
theorem readIndexPayload_spec (C : Ctx) (markers target : Fin MM) (hne : target ≠ markers)
    (count : Fin VV) (hcount : count ∉ fieldIndex :: signedStreamScratch)
    (values : List ℤ) (B q : ℕ) (rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = values.flatMap NearCubicGates.Close.Interfaces.intWord ++ rest)
    (hbits : ∀ z ∈ values, natBitLength z.natAbs ≤ B)
    (hq : 2 ≤ q) (haq : a.env modulusVar = q) (hfit : 2 * q ≤ 2 ^ C.Wd) (hW : 3 ≤ C.Wd)
    (hcountValue : a.env count = values.length) (hcountFit : values.length < 2 ^ C.Wd)
    (hcursor : a.rc target = (a.ram target).length) :
    Hs C (readIndexPayload markers target count) a
      (values.length * (a.rc markers + 31 * B + 127) + 4) (fun b =>
      b.ip = a.ip + (values.flatMap NearCubicGates.Close.Interfaces.intWord).length ∧
      b.ram target = a.ram target ++ values.map (fun z => (z % (q : ℤ)).toNat) ∧
      b.rc target = a.rc target + values.length ∧ b.rc markers ≤ a.rc markers + B + 1 ∧
      (∀ other, other ≠ markers → other ≠ target →
        b.ram other = a.ram other ∧ b.rc other = a.rc other) ∧
      (b.out, b.kin, b.kout, b.kc) = (a.out, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b (fieldIndex :: signedStreamScratch)) := by
  have hneCount : fieldIndex ≠ count := by intro h; exact hcount (by simp [← h])
  let I (k : ℕ) (b : DS VV MM) : Prop :=
    b.ip = a.ip + ((values.take k).flatMap NearCubicGates.Close.Interfaces.intWord).length ∧
    b.ram target = a.ram target ++ (values.take k).map (fun z => (z % (q : ℤ)).toNat) ∧
    b.rc target = a.rc target + k ∧ b.rc markers ≤ a.rc markers + B + 1 ∧
    (∀ other, other ≠ markers → other ≠ target →
      b.ram other = a.ram other ∧ b.rc other = a.rc other) ∧
    (b.out, b.kin, b.kout, b.kc) = (a.out, a.kin, a.kout, a.kc) ∧
    Cst b ∧ Fr a b (fieldIndex :: signedStreamScratch)
  have hIi : ∀ k b v, I k b → I k (b.set fieldIndex v) := by
    intro k b v ⟨hi, hr, hrc, hm, ho, hs, hbc, hf⟩
    exact ⟨hi, hr, hrc, hm, ho, hs,
      Cst.of_fr (T := [fieldIndex]) hbc (Fr.set b v (by simp)) (by decide),
      hf.trans (Fr.set b v (by simp))⟩
  have h0 : I 0 a :=
    ⟨by simp, by simp, by simp, by omega, fun _ _ _ => ⟨rfl, rfl⟩, rfl, hc, Fr.refl _ _⟩
  unfold readIndexPayload
  refine (forS_spec' (C := C) fieldIndex count hneCount (readIndexInteger markers target)
    a values.length hcountFit I (a.rc markers + 31 * B + 123) hIi h0 hcountValue ?_).mono
      le_rfl ?_
  · intro k hk b ⟨hbi, hbr, hbrc, hbmc, hbo, hbsh, hbc, hbf⟩ hki hcn
    have hsplit : values.flatMap NearCubicGates.Close.Interfaces.intWord =
        (values.take k).flatMap NearCubicGates.Close.Interfaces.intWord ++
          NearCubicGates.Close.Interfaces.intWord values[k] ++
          (values.drop (k + 1)).flatMap NearCubicGates.Close.Interfaces.intWord := by
      conv_lhs => rw [← List.take_append_drop k values]
      rw [List.flatMap_append, List.drop_eq_getElem_cons hk, List.flatMap_cons, List.append_assoc]
    have hbin : C.inp.drop b.ip = NearCubicGates.Close.Interfaces.intWord values[k] ++
        ((values.drop (k + 1)).flatMap NearCubicGates.Close.Interfaces.intWord ++ rest) := by
      rw [hbi, ← List.drop_drop, hin, hsplit, List.append_assoc, List.append_assoc, List.drop_left]
    have hbq : b.env modulusVar = q := by rw [hbf _ (by decide)]; exact haq
    have hbcursor : b.rc target = (b.ram target).length := by
      rw [hbr, List.length_append, List.length_map, List.length_take, min_eq_left hk.le, hbrc, hcursor]
    have hvalueBits := hbits values[k] (List.getElem_mem hk)
    refine (readIndexInteger_spec C markers target hne values[k]
      ((values.drop (k + 1)).flatMap NearCubicGates.Close.Interfaces.intWord ++ rest)
      b hbc q hq hbq hfit hW hbin hbcursor).mono (by omega) ?_
    rintro d ⟨hdr, hdrc, _hdm, hdmc, hdi, hdo, hdsh, hdc, hdf⟩
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, hdsh.trans hbsh, hdc,
      hbf.trans (hdf.weaken (fun _ hx => List.mem_cons_of_mem _ hx))⟩, ?_, ?_⟩
    · rw [hdi, hbi, List.take_succ_eq_append_getElem hk, List.flatMap_append,
        List.flatMap_singleton, List.length_append]
      omega
    · rw [hdr, hbr, List.take_succ_eq_append_getElem hk, List.map_append, List.map_singleton,
        List.append_assoc]
    · rw [hdrc, hbrc]
      omega
    · rw [hdmc]
      omega
    · intro other hm ht
      obtain ⟨hr₁, hc₁⟩ := hdo other hm ht
      obtain ⟨hr₂, hc₂⟩ := hbo other hm ht
      exact ⟨hr₁.trans hr₂, hc₁.trans hc₂⟩
    · rw [hdf fieldIndex (by decide)]
      exact hki
    · rw [hdf count (by intro h; exact hcount (List.mem_cons_of_mem _ h))]
      exact hcn
  · rintro b ⟨hb, _, _⟩
    simpa only [I, List.take_length] using hb

end NearQuarticWires.StageLift
