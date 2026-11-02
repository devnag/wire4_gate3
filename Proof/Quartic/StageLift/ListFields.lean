import Proof.Quartic.StageLift.CountedFields
import Proof.Quartic.StageRecovery.PacketFields

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

/-- `sec:params` and `lem:print`, paper/paper.tex: decode an actual list-length header followed by every
natural field of its prime or factor payload. -/
def readListFields (store : Fin MM) (count : Fin VV) : St VV MM :=
  .seq (StageRecovery.readVariable count) (readCountedFields store count)

/-- `sec:params` and `lem:print`, paper/paper.tex: the full natural-list codec is consumed from its
original bytes; the list and its length are retained physically. -/
theorem readListFields_spec (C : Ctx) (store : Fin MM) (count : Fin VV)
    (hcount : count ∉ fieldIndex :: rdNatT)
    (hconst : count ≠ vZ ∧ count ≠ v1 ∧ count ≠ v2)
    (values : List ℕ) (B : ℕ) (rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = listWord natWord values ++ rest)
    (hwidth : ∀ value ∈ values, natBitLength value ≤ B)
    (hB : B + 2 ≤ C.Wd) (hcountWidth : natBitLength values.length + 2 ≤ C.Wd)
    (hcountFit : values.length < 2 ^ C.Wd)
    (hcursor : a.rc store = (a.ram store).length) :
    Hs C (readListFields store count) a
      (30 * natBitLength values.length + values.length * (30 * B + 39) + 37) (fun b =>
      b.env count = values.length ∧ b.ip = a.ip + (listWord natWord values).length ∧
      b.ram store = a.ram store ++ values ∧ b.rc store = a.rc store + values.length ∧
      (∀ other, other ≠ store → b.ram other = a.ram other ∧ b.rc other = a.rc other) ∧
      (b.out, b.kin, b.kout, b.kc) = (a.out, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b (count :: fieldIndex :: rdNatT)) := by
  unfold readListFields
  have her := StageRecovery.readVariable_spec C a hc count
    (by intro h; exact hcount (List.mem_cons_of_mem _ h)) hconst values.length
    (values.flatMap natWord ++ rest) (by simpa only [listWord, List.append_assoc] using hin) hcountWidth
  refine (Hs.seq (t2 := values.length * (30 * B + 39) + 4) her
    fun b ⟨hbn, hbi, hbr, hbc, hbf⟩ => ?_).mono (by omega) (fun _ h => h)
  have hbo : b.out = a.out := congrArg (fun t => t.1) hbr
  have hbram : b.ram = a.ram := congrArg (fun t => t.2.1) hbr
  have hbrc : b.rc = a.rc := congrArg (fun t => t.2.2.1) hbr
  have hbkin : b.kin = a.kin := congrArg (fun t => t.2.2.2.1) hbr
  have hbkout : b.kout = a.kout := congrArg (fun t => t.2.2.2.2.1) hbr
  have hbkc : b.kc = a.kc := congrArg (fun t => t.2.2.2.2.2) hbr
  have hbin : C.inp.drop b.ip = values.flatMap natWord ++ rest := by
    rw [hbi, ← List.drop_drop, hin, listWord, List.append_assoc, List.drop_left]
  refine (readCountedFields_spec C store count hcount values B rest b hbc hbin hwidth hB
    hbn hcountFit (by rw [hbrc, hbram]; exact hcursor)).mono le_rfl ?_
  rintro d ⟨hdi, hdr, hdrc, hdother, hdsh, hdc, hdf⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hdc, ?_⟩
  · rw [hdf count hcount, hbn]
  · rw [hdi, hbi, listWord, List.length_append]
    omega
  · rw [hdr, hbram]
  · rw [hdrc, hbrc]
  · intro other hother
    simpa only [hbram, hbrc] using hdother other hother
  · simpa only [hbo, hbkin, hbkout, hbkc] using hdsh
  · exact Fr.trans (hbf.weaken (by
      intro y hy
      simp only [List.mem_cons] at hy ⊢
      tauto)) (hdf.weaken (by intro y hy; exact List.mem_cons_of_mem _ hy))

end NearQuarticWires.StageLift
