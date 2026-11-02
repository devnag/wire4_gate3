import Proof.Quartic.StageMainMask.CallData
import Proof.Quartic.StageMainMask.StoredInput

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces
open StageMain StageMain.Compact StageLift

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
the shared structural call is selected and receives the actual retained
preparation word and the two computed pattern indices in binary. -/
def emitStructuralInput : St VV MM := .seq (.op (.kem false))
  (.seq (emitStoredInput compactStore 39) (emitNaturalFields [(27, 0), (28, 0)]))

/-- Step 4 of `sec:algorithm` and `prop:time`, paper/paper.tex: the original preparation source is
copied physically, the actual sample indices are printed in binary,
and the exact tagged structural-request bytes are charged linearly. -/
theorem emitStructuralInput_run {B1 B2 : ℕ} (C : Ctx) (r : EntryRequest B1 B2)
    (a : DS VV MM) (hc : Cst a) (ha : EntryNumericData r a) (hkin : a.kin = [])
    (hW : 2 ≤ C.Wd)
    (hprep : (Program.prepWord B1 B2 r.call r.witness).length < 2 ^ C.Wd)
    (hleft : natBitLength (entryPosition r).1.val + 2 < 2 ^ C.Wd)
    (hright : natBitLength (entryPosition r).2.val + 2 < 2 ^ C.Wd)
    (hroom : 1 + (structuralWord (entryStructuralRequest r)).length ≤ C.Lk) :
    Hs C emitStructuralInput a
      (a.rc compactStore + 8 * (Program.prepWord B1 B2 r.call r.witness).length +
        40 * natBitLength (entryPosition r).1.val + 40 * natBitLength (entryPosition r).2.val + 100)
      (fun b => b.kin = false :: structuralWord (entryStructuralRequest r) ∧
        b.ip = a.ip ∧ b.out = a.out ∧ b.ram = a.ram ∧ b.kout = a.kout ∧ b.kc = a.kc ∧
        Cst b ∧ Fr a b sourceWriterScratch ∧ EntryNumericData r b) := by
  let prep := Program.prepWord B1 B2 r.call r.witness
  let fields : List (Fin VV × ℕ) := [(27, (entryPosition r).1.val), (28, (entryPosition r).2.val)]
  have hr : 1 + prep.length + (natWord (entryPosition r).1.val).length +
      (natWord (entryPosition r).2.val).length ≤ C.Lk := by
    simpa only [structuralWord, entryStructuralRequest, List.length_append, Nat.add_assoc, prep] using hroom
  change Hs C (.seq (.op (.kem false)) (.seq (emitStoredInput compactStore 39)
    (emitNaturalFields fields))) a _ _
  refine (Hs.seq (t1 := 1)
    (t2 := a.rc compactStore + 8 * prep.length + 6 + naturalFieldsCost fields + 1)
    (hs_kem C false a (by rw [hkin]; simp only [List.length_nil]; omega)) ?_).mono
      (by simp [naturalFieldsCost, fields, prep]; omega) (fun _ h => h)
  rintro d rfl
  let d : DS VV MM := { a with kin := a.kin ++ [false] }
  have hdc : Cst d := ⟨hc.z, hc.one, hc.two⟩
  have hdk : d.kin = [false] := by simp [d, hkin]
  refine Hs.seq (t1 := a.rc compactStore + 8 * prep.length + 6)
    (t2 := naturalFieldsCost fields)
    (emitStoredInput_run C compactStore 39 (by decide) prep d hdc ha.prepared
      ha.preparedLength hprep (by rw [hdk]; simp only [List.length_singleton]; omega)) ?_
  rintro b ⟨hbkin, hbip, hbout, hbram, _hbrc, hbkout, hbkc, hbc, hbfr⟩
  have hbk : b.kin = [false] ++ prep := by rw [hbkin, hdk]
  have hvalues : ∀ p ∈ fields, b.env p.1 = p.2 := by
    intro p hp
    simp only [fields, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact (hbfr 27 (by decide)).trans ha.left
    · exact (hbfr 28 (by decide)).trans ha.right
  have hregs : ∀ p ∈ fields, p.1 ∉ t3 :: emitNatT := by
    intro p hp
    simp only [fields, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · change (27 : Fin VV) ∉ t3 :: emitNatT
      decide
    · change (28 : Fin VV) ∉ t3 :: emitNatT
      decide
  have hfit : ∀ p ∈ fields, natBitLength p.2 + 2 < 2 ^ C.Wd := by
    intro p hp
    simp only [fields, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact hleft
    · exact hright
  refine (emitNaturalFields_run C fields hregs b hbc hvalues hW hfit (by
    rw [hbk]
    simpa only [fields, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.length_append, List.length_singleton, Nat.add_assoc] using hr)).mono le_rfl ?_
  rintro e ⟨hekin, herest, hec, hefr⟩
  rcases (by simpa only [Prod.mk.injEq] using herest) with ⟨hei, heo, hem, _herc, heko, hekc⟩
  have hef : Fr a e sourceWriterScratch :=
    (hbfr.weaken (by simp [sourceWriterScratch])).trans (hefr.weaken (by
      intro x hx
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
        sourceWriterScratch] at hx ⊢
      tauto))
  have herm : e.ram = a.ram := hem.trans hbram
  refine ⟨?_, hei.trans hbip, heo.trans hbout, herm, heko.trans hbkout, hekc.trans hbkc,
    hec, hef, ha.of_writer herm hef⟩
  rw [hekin, hbk]
  simp only [fields, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    structuralWord, entryStructuralRequest, List.cons_append, List.nil_append, List.append_assoc, prep]

end NearQuarticWires.StageMainMask
