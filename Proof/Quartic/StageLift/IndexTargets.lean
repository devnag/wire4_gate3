import Proof.Quartic.StageLift.IndexList

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open NearQuarticWires.StageRecovery

/-- `lem:print`, paper/paper.tex: both original
signed target lists are streamed once into the same bounded record bank. -/
def readIndexTargets (markers target : Fin MM) (count : Fin VV) : St VV MM :=
  .seq (readIndexList markers target count) (readIndexList markers target count)

/-- `lem:print`, paper/paper.tex: the actual two
list counts control one-time normalization of all raw digit and score
values. Their unbounded bit lengths enter only this additive polynomial
input-processing cost, not any per-walk source or arithmetic width. -/
theorem readIndexTargets_spec (C : Ctx) (markers target : Fin MM) (hne : target ≠ markers)
    (count : Fin VV) (hcount : count ∉ fieldIndex :: signedStreamScratch)
    (hcountMod : count ≠ modulusVar) (hconst : count ≠ vZ ∧ count ≠ v1 ∧ count ≠ v2)
    (digits residues : List ℤ) (B q : ℕ) (rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = listWord NearCubicGates.Close.Interfaces.intWord digits ++
      listWord NearCubicGates.Close.Interfaces.intWord residues ++ rest)
    (hbits : ∀ z ∈ digits ++ residues, natBitLength z.natAbs ≤ B)
    (hq : 2 ≤ q) (haq : a.env modulusVar = q) (hfit : 2 * q ≤ 2 ^ C.Wd) (hW : 3 ≤ C.Wd)
    (hcountWidths : natBitLength digits.length + 2 ≤ C.Wd ∧
      natBitLength residues.length + 2 ≤ C.Wd)
    (hcountFits : digits.length < 2 ^ C.Wd ∧ residues.length < 2 ^ C.Wd)
    (hcursor : a.rc target = (a.ram target).length) :
    Hs C (readIndexTargets markers target count) a
      ((digits.length + residues.length) * (a.rc markers + 32 * B + 128) +
        30 * (natBitLength digits.length + natBitLength residues.length) + 75) (fun b =>
      b.ip = a.ip + (listWord NearCubicGates.Close.Interfaces.intWord digits).length +
        (listWord NearCubicGates.Close.Interfaces.intWord residues).length ∧
      b.ram target = a.ram target ++ (digits ++ residues).map (fun z => (z % (q : ℤ)).toNat) ∧
      b.rc target = a.rc target + digits.length + residues.length ∧
      b.rc markers ≤ a.rc markers + 2 * B + 2 ∧
      (∀ other, other ≠ markers → other ≠ target →
        b.ram other = a.ram other ∧ b.rc other = a.rc other) ∧
      (b.out, b.kin, b.kout, b.kc) = (a.out, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b (count :: fieldIndex :: signedStreamScratch)) := by
  unfold readIndexTargets
  refine (Hs.seq
    (t1 := 30 * natBitLength digits.length + digits.length * (a.rc markers + 31 * B + 127) + 37)
    (t2 := 30 * natBitLength residues.length + residues.length * (a.rc markers + 32 * B + 128) + 37)
    (readIndexList_spec C markers target hne count hcount hcountMod hconst digits B q
      (listWord NearCubicGates.Close.Interfaces.intWord residues ++ rest) a hc
      (by simpa only [List.append_assoc] using hin)
      (by intro z hz; exact hbits z (List.mem_append_left _ hz)) hq haq hfit hW
      hcountWidths.1 hcountFits.1 hcursor)
    fun b ⟨_hbn, hbi, hbr, hbrc, hbmc, hbo, hbsh, hbc, hbf⟩ => ?_).mono
      (by nlinarith) (fun _ h => h)
  have hbq : b.env modulusVar = q := by
    rw [hbf _ (by
      intro hm
      rcases List.mem_cons.mp hm with hm | hm
      · exact hcountMod hm.symm
      · exact (by decide : modulusVar ∉ fieldIndex :: signedStreamScratch) hm)]
    exact haq
  have hbin : C.inp.drop b.ip = listWord NearCubicGates.Close.Interfaces.intWord residues ++ rest := by
    rw [hbi, ← List.drop_drop, hin, List.append_assoc, List.drop_left]
  have hbcursor : b.rc target = (b.ram target).length := by
    rw [hbr, hbrc, List.length_append, List.length_map, hcursor]
  refine (readIndexList_spec C markers target hne count hcount hcountMod hconst residues B q rest b hbc hbin
    (by intro z hz; exact hbits z (List.mem_append_right _ hz)) hq hbq hfit hW hcountWidths.2
    hcountFits.2 hbcursor).mono (by nlinarith) ?_
  rintro d ⟨_hdn, hdi, hdr, hdrc, hdmc, hdo, hdsh, hdc, hdf⟩
  refine ⟨by rw [hdi, hbi], ?_, ?_, ?_, ?_, hdsh.trans hbsh, hdc, hbf.trans hdf⟩
  · rw [hdr, hbr, List.map_append, List.append_assoc]
  · rw [hdrc, hbrc]
  · omega
  · intro other hm ht
    obtain ⟨hr₁, hc₁⟩ := hdo other hm ht
    obtain ⟨hr₂, hc₂⟩ := hbo other hm ht
    exact ⟨hr₁.trans hr₂, hc₁.trans hc₂⟩

end NearQuarticWires.StageLift
