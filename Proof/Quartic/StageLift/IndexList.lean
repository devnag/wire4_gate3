import Proof.Quartic.StageLift.IndexPayload
import Proof.Quartic.StageRecovery.PacketFields

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open NearQuarticWires.StageRecovery

/-- `lem:print`, paper/paper.tex: the original
signed-list length is read physically before streaming its raw fields
once into the bounded normalized index bank. -/
def readIndexList (markers target : Fin MM) (count : Fin VV) : St VV MM :=
  .seq (readVariable count) (readIndexPayload markers target count)

/-- `lem:print`, paper/paper.tex: the complete
original signed-list codec is consumed, including its actual header.
Raw field lengths affect only the additive input-processing budget;
the arithmetic width depends on q and the bounded list count. -/
theorem readIndexList_spec (C : Ctx) (markers target : Fin MM) (hne : target ≠ markers)
    (count : Fin VV) (hcount : count ∉ fieldIndex :: signedStreamScratch)
    (hcountMod : count ≠ modulusVar) (hconst : count ≠ vZ ∧ count ≠ v1 ∧ count ≠ v2)
    (values : List ℤ) (B q : ℕ) (rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = listWord NearCubicGates.Close.Interfaces.intWord values ++ rest)
    (hbits : ∀ z ∈ values, natBitLength z.natAbs ≤ B)
    (hq : 2 ≤ q) (haq : a.env modulusVar = q) (hfit : 2 * q ≤ 2 ^ C.Wd) (hW : 3 ≤ C.Wd)
    (hcountWidth : natBitLength values.length + 2 ≤ C.Wd)
    (hcountFit : values.length < 2 ^ C.Wd)
    (hcursor : a.rc target = (a.ram target).length) :
    Hs C (readIndexList markers target count) a
      (30 * natBitLength values.length +
        values.length * (a.rc markers + 31 * B + 127) + 37) (fun b =>
      b.env count = values.length ∧
      b.ip = a.ip + (listWord NearCubicGates.Close.Interfaces.intWord values).length ∧
      b.ram target = a.ram target ++ values.map (fun z => (z % (q : ℤ)).toNat) ∧
      b.rc target = a.rc target + values.length ∧ b.rc markers ≤ a.rc markers + B + 1 ∧
      (∀ other, other ≠ markers → other ≠ target →
        b.ram other = a.ram other ∧ b.rc other = a.rc other) ∧
      (b.out, b.kin, b.kout, b.kc) = (a.out, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b (count :: fieldIndex :: signedStreamScratch)) := by
  have hreadSafe : count ∉ rdNatT := by
    intro hm
    exact hcount (by
      simp only [List.mem_cons, signedStreamScratch, List.mem_append]
      tauto)
  have her := readVariable_spec C a hc count hreadSafe hconst values.length
    (values.flatMap NearCubicGates.Close.Interfaces.intWord ++ rest)
    (by simpa only [listWord, List.append_assoc] using hin) hcountWidth
  unfold readIndexList
  refine (Hs.seq
    (t2 := values.length * (a.rc markers + 31 * B + 127) + 4) her
    fun b ⟨hbn, hbi, hbrest, hbc, hbf⟩ => ?_).mono (by omega) (fun _ h => h)
  have hbram : b.ram = a.ram := congrArg (fun t => t.2.1) hbrest
  have hbrc : b.rc = a.rc := congrArg (fun t => t.2.2.1) hbrest
  have hbsmall : (b.out, b.kin, b.kout, b.kc) = (a.out, a.kin, a.kout, a.kc) :=
    congrArg (fun t => (t.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2)) hbrest
  have hbq : b.env modulusVar = q := by
    rw [hbf _ (by
      intro hm
      rcases List.mem_cons.mp hm with hm | hm
      · exact hcountMod hm.symm
      · exact (by decide : modulusVar ∉ rdNatT) hm)]
    exact haq
  have hbin : C.inp.drop b.ip =
      values.flatMap NearCubicGates.Close.Interfaces.intWord ++ rest := by
    rw [hbi, ← List.drop_drop, hin, listWord, List.append_assoc, List.drop_left]
  have he := readIndexPayload_spec C markers target hne count hcount values B q rest b hbc
    hbin hbits hq hbq hfit hW hbn hcountFit (by rw [hbrc, hbram]; exact hcursor)
  rw [hbrc] at he
  refine he.mono le_rfl ?_
  rintro d ⟨hdi, hdr, hdrc, hdmc, hdo, hdsh, hdc, hdf⟩
  refine ⟨by rw [hdf count hcount, hbn], ?_, ?_, ?_, ?_, ?_, hdsh.trans hbsmall, hdc, ?_⟩
  · rw [hdi, hbi, listWord, List.length_append]
    omega
  · rw [hdr, hbram]
  · exact hdrc
  · exact hdmc
  · intro other hm ht
    simpa only [hbram, hbrc] using hdo other hm ht
  · exact (hbf.weaken (by
      intro x hx
      simp only [List.mem_cons, signedStreamScratch, List.mem_append] at hx ⊢
      tauto)).trans (hdf.weaken (fun _ hx => List.mem_cons_of_mem _ hx))

end NearQuarticWires.StageLift
