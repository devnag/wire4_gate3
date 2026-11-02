import Proof.Quartic.StageMainMask.CallData
import Proof.Quartic.StageMainMask.StoredFrameInput

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageMain StageMain.Compact StageLift

/-- `def:mask` and Step 4 of `sec:algorithm`, paper/paper.tex: the actual selection offset and
four computed corners occur in the literal population-source order. -/
noncomputable def populationInputFields {B1 B2 : ℕ} (r : EntryRequest B1 B2) :
    List (Fin VV × ℕ) :=
  [(38, r.selected.1.k), (114, entryCorners r 0), (115, entryCorners r 1),
    (116, entryCorners r 2), (117, entryCorners r 3)]

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
the population request is selected, then the complete original call,
computed numeric metadata and actual finite witness frame are emitted. -/
def emitPopulationInput : St VV MM := .seq (.op (.kem true))
  (.seq (.op (.kem false)) (.seq (emitStoredInput callStore 40)
    (.seq (emitNaturalFields [(38, 0), (114, 0), (115, 0), (116, 0), (117, 0)])
      (emitStoredFrameInput witnessStore 42))))

/-- `def:mask`, paper/paper.tex: binary scalar
printing agrees with the population request's exact five-field codec. -/
theorem populationInputFields_word {B1 B2 : ℕ} (r : EntryRequest B1 B2) :
    (populationInputFields r).flatMap (fun p => natWord p.2) =
      natWord r.selected.1.k ++ (List.ofFn (entryCorners r)).flatMap natWord := by
  simp [populationInputFields, List.ofFn_succ]

/-- Step 4 of `sec:algorithm` and `prop:time`, paper/paper.tex: every original source bit, binary
corner field and witness-frame marker is physically emitted, with no
decoded gate bank, selected population or point supplied separately. -/
theorem emitPopulationInput_run {B1 B2 : ℕ} (C : Ctx) (r : EntryRequest B1 B2)
    (a : DS VV MM) (hc : Cst a) (ha : EntryNumericData r a) (hkin : a.kin = [])
    (hW : 2 ≤ C.Wd) (hcall : (callWord r.call).length < 2 ^ C.Wd)
    (hwit : (Program.witnessPrefix r.call r.selected.1 r.witness).length < 2 ^ C.Wd)
    (hfit : ∀ p ∈ populationInputFields r, natBitLength p.2 + 2 < 2 ^ C.Wd)
    (hroom : 2 + (entryPopulationRequest r).word.length ≤ C.Lk) :
    Hs C emitPopulationInput a
      (a.rc callStore + a.rc witnessStore + 8 * (callWord r.call).length +
        10 * (Program.witnessPrefix r.call r.selected.1 r.witness).length +
        naturalFieldsCost (populationInputFields r) + 30)
      (fun b => b.kin = true :: false :: (entryPopulationRequest r).word ∧
        b.ip = a.ip ∧ b.out = a.out ∧ b.ram = a.ram ∧ b.kout = a.kout ∧ b.kc = a.kc ∧
        Cst b ∧ Fr a b sourceWriterScratch ∧ EntryNumericData r b) := by
  let fields := populationInputFields r
  let wit := Program.witnessPrefix r.call r.selected.1 r.witness
  have hr : 2 + (callWord r.call).length +
      (fields.flatMap (fun p => natWord p.2)).length + (frame wit).length ≤ C.Lk := by
    rw [populationInputFields_word]
    simpa only [PopulationRequest.word, entryPopulationRequest, List.length_append,
      Nat.add_assoc, wit] using hroom
  change Hs C (.seq (.op (.kem true)) (.seq (.op (.kem false))
    (.seq (emitStoredInput callStore 40) (.seq (emitNaturalFields fields)
      (emitStoredFrameInput witnessStore 42))))) a _ _
  refine (Hs.seq (t1 := 1) (t2 := a.rc callStore + a.rc witnessStore +
    8 * (callWord r.call).length + 10 * wit.length + naturalFieldsCost fields + 26)
    (hs_kem C true a (by rw [hkin]; simp only [List.length_nil]; omega)) ?_).mono
      (by dsimp [fields, wit]; omega) (fun _ h => h)
  rintro d rfl
  let d : DS VV MM := { a with kin := a.kin ++ [true] }
  have hdc : Cst d := ⟨hc.z, hc.one, hc.two⟩
  refine (Hs.seq (t1 := 1) (t2 := a.rc callStore + a.rc witnessStore +
    8 * (callWord r.call).length + 10 * wit.length + naturalFieldsCost fields + 23)
    (hs_kem C false d (by change (a.kin ++ [true]).length < C.Lk; rw [hkin]; simp; omega)) ?_).mono
      (by omega) (fun _ h => h)
  rintro e rfl
  let e : DS VV MM := { d with kin := d.kin ++ [false] }
  have hec : Cst e := ⟨hc.z, hc.one, hc.two⟩
  have hek : e.kin = [true, false] := by simp [e, d, hkin]
  refine (Hs.seq (t1 := a.rc callStore + 8 * (callWord r.call).length + 6)
    (t2 := naturalFieldsCost fields + (a.rc witnessStore + 10 * wit.length + 8) + 1)
    (emitStoredInput_run C callStore 40 (by decide) (callWord r.call) e hec ha.originalCall
      ha.callLength hcall (by rw [hek]; simp only [List.length_cons, List.length_nil]; omega)) ?_).mono
      (by omega) (fun _ h => h)
  rintro b ⟨hbkin, hbip, hbout, hbram, hbrc, hbkout, hbkc, hbc, hbfr⟩
  have hbk : b.kin = [true, false] ++ callWord r.call := by rw [hbkin, hek]
  have hregs : ∀ p ∈ fields, p.1 ∉ t3 :: emitNatT := by
    intro p hp
    simp only [fields, populationInputFields, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide
  have hvalues : ∀ p ∈ fields, b.env p.1 = p.2 := by
    intro p hp
    simp only [fields, populationInputFields, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact (hbfr 38 (by decide)).trans ha.offset
    · exact (hbfr 114 (by decide)).trans (ha.corners 0)
    · exact (hbfr 115 (by decide)).trans (ha.corners 1)
    · exact (hbfr 116 (by decide)).trans (ha.corners 2)
    · exact (hbfr 117 (by decide)).trans (ha.corners 3)
  refine Hs.seq (t1 := naturalFieldsCost fields)
    (t2 := a.rc witnessStore + 10 * wit.length + 8)
    (emitNaturalFields_run C fields hregs b hbc hvalues hW hfit (by
      rw [hbk, List.length_append]
      change 2 + (callWord r.call).length + _ ≤ C.Lk
      omega)) ?_
  rintro f ⟨hfkin, hfrest, hfc, hffr⟩
  rcases (by simpa only [Prod.mk.injEq] using hfrest) with ⟨hfi, hfo, hfm, hfrc, hfko, hfkc⟩
  have hfk : f.kin = ([true, false] ++ callWord r.call) ++ fields.flatMap (fun p => natWord p.2) := by
    rw [hfkin, hbk]
  have hfrc' : f.rc witnessStore = a.rc witnessStore := by
    rw [hfrc, hbrc, Function.update_of_ne (by decide : witnessStore ≠ callStore)]
  have hff : Fr a f sourceWriterScratch :=
    (hbfr.weaken (by simp [sourceWriterScratch])).trans (hffr.weaken (by
      intro x hx
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
        sourceWriterScratch] at hx ⊢
      tauto))
  have hfrm : f.ram = a.ram := hfm.trans hbram
  refine ((emitStoredFrameInput_run C witnessStore 42 (by decide) wit f hfc
    (hfrm ▸ ha.witness) ((hff _ (by decide)).trans ha.witnessLength) hwit (by
      rw [hfk]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega)).mono (by rw [hfrc']) (fun _ h => h)).mono le_rfl ?_
  rintro g ⟨hgkin, hgi, hgm, _hgrc, hgrest, hgc, hgfr⟩
  rcases (by simpa only [Prod.mk.injEq] using hgrest) with ⟨hgo, hgko, hgkc⟩
  have hgf : Fr a g sourceWriterScratch :=
    hff.trans (hgfr.weaken (by simp [sourceWriterScratch]))
  have hgrm : g.ram = a.ram := hgm.trans hfrm
  refine ⟨?_, hgi.trans (hfi.trans hbip), hgo.trans (hfo.trans hbout), hgrm,
    hgko.trans (hfko.trans hbkout), hgkc.trans (hfkc.trans hbkc), hgc, hgf, ha.of_writer hgrm hgf⟩
  rw [hgkin, hfk, populationInputFields_word]
  simp only [PopulationRequest.word, entryPopulationRequest, List.cons_append,
    List.nil_append, List.append_assoc, wit]

end NearQuarticWires.StageMainMask
