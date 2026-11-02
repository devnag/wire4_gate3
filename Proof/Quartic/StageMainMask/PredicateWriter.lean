import Proof.Quartic.StageMainMask.CallData
import Proof.Quartic.StageMainMask.StoredInput
import Proof.Quartic.StageMainMask.EntryValues

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open StageMain StageMain.Compact StageLift

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
the predicate branch receives the actual both-error packed point and
the complete retained original call, with two physical selector bits. -/
def emitPredicateInput : St VV MM := .seq (.op (.kem true))
  (.seq (.op (.kem true)) (.seq (emitNaturalFields [(117, 0)]) (emitStoredInput callStore 40)))

/-- Step 4 of `sec:algorithm` and `prop:time`, paper/paper.tex: the actual computed original point
is printed in binary and the literal complete circuit source is copied
to the predicate subroutine with every ordinary input bit charged. -/
theorem emitPredicateInput_run {B1 B2 : ℕ} (C : Ctx) (r : EntryRequest B1 B2)
    (a : DS VV MM) (hc : Cst a) (ha : EntryNumericData r a) (hkin : a.kin = [])
    (hW : 2 ≤ C.Wd) (hcall : (callWord r.call).length < 2 ^ C.Wd)
    (hpoint : natBitLength (entryPredicateRequest r).point + 2 < 2 ^ C.Wd)
    (hroom : 2 + (entryPredicateRequest r).word.length ≤ C.Lk) :
    Hs C emitPredicateInput a
      (a.rc callStore + 8 * (callWord r.call).length +
        40 * natBitLength (entryPredicateRequest r).point + 60)
      (fun b => b.kin = true :: true :: (entryPredicateRequest r).word ∧
        b.ip = a.ip ∧ b.out = a.out ∧ b.ram = a.ram ∧ b.kout = a.kout ∧ b.kc = a.kc ∧
        Cst b ∧ Fr a b sourceWriterScratch ∧ EntryNumericData r b) := by
  let fields : List (Fin VV × ℕ) := [(117, (entryPredicateRequest r).point)]
  have hr : 2 + (natWord (entryPredicateRequest r).point).length + (callWord r.call).length ≤ C.Lk := by
    simpa only [PredicateRequest.word, entryPredicateRequest, List.length_append, Nat.add_assoc] using hroom
  change Hs C (.seq (.op (.kem true)) (.seq (.op (.kem true))
    (.seq (emitNaturalFields fields) (emitStoredInput callStore 40)))) a _ _
  refine (Hs.seq (t1 := 1) (t2 := naturalFieldsCost fields +
    (a.rc callStore + 8 * (callWord r.call).length + 6) + 3)
    (hs_kem C true a (by rw [hkin]; simp only [List.length_nil]; omega)) ?_).mono
      (by simp [naturalFieldsCost, fields]; omega) (fun _ h => h)
  rintro d rfl
  let d : DS VV MM := { a with kin := a.kin ++ [true] }
  have hdc : Cst d := ⟨hc.z, hc.one, hc.two⟩
  refine (Hs.seq (t1 := 1) (t2 := naturalFieldsCost fields +
    (a.rc callStore + 8 * (callWord r.call).length + 6) + 1)
    (hs_kem C true d (by change (a.kin ++ [true]).length < C.Lk; rw [hkin]; simp; omega)) ?_).mono
      (by omega) (fun _ h => h)
  rintro e rfl
  let e : DS VV MM := { d with kin := d.kin ++ [true] }
  have hec : Cst e := ⟨hc.z, hc.one, hc.two⟩
  have hek : e.kin = [true, true] := by simp [e, d, hkin]
  have hregs : ∀ p ∈ fields, p.1 ∉ t3 :: emitNatT := by
    intro p hp
    simp only [fields, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst p
    change (117 : Fin VV) ∉ t3 :: emitNatT
    decide
  have hvalues : ∀ p ∈ fields, e.env p.1 = p.2 := by
    intro p hp
    simp only [fields, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst p
    exact ha.corners 3
  have hfit : ∀ p ∈ fields, natBitLength p.2 + 2 < 2 ^ C.Wd := by
    intro p hp
    simp only [fields, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst p
    exact hpoint
  refine Hs.seq (t1 := naturalFieldsCost fields)
    (t2 := a.rc callStore + 8 * (callWord r.call).length + 6)
    (emitNaturalFields_run C fields hregs e hec hvalues hW hfit (by
      rw [hek]
      simp only [fields, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.length_cons, List.length_nil]
      omega)) ?_
  rintro b ⟨hbkin, hbrest, hbc, hbfr⟩
  rcases (by simpa only [Prod.mk.injEq] using hbrest) with ⟨hbi, hbo, hbm, hbrc, hbko, hbkc⟩
  have hbk : b.kin = [true, true] ++ natWord (entryPredicateRequest r).point := by
    simpa only [fields, List.flatMap_cons, List.flatMap_nil, List.append_nil, hek] using hbkin
  have hbf : Fr a b sourceWriterScratch := hbfr.weaken (by
    intro x hx
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
      sourceWriterScratch] at hx ⊢
    tauto)
  refine ((emitStoredInput_run C callStore 40 (by decide) (callWord r.call) b hbc
    (hbm ▸ ha.originalCall) ((hbf _ (by decide)).trans ha.callLength) hcall (by
      rw [hbk]
      simpa only [List.length_append, List.length_cons, List.length_nil] using hr)).mono
      (by rw [hbrc]) (fun _ h => h)).mono le_rfl ?_
  rintro f ⟨hfkin, hfi, hfo, hfm, _hfrc, hfko, hfkc, hfc, hffr⟩
  have hff : Fr a f sourceWriterScratch :=
    hbf.trans (hffr.weaken (by simp [sourceWriterScratch]))
  have hfrm : f.ram = a.ram := hfm.trans hbm
  refine ⟨?_, hfi.trans hbi, hfo.trans hbo, hfrm, hfko.trans hbko, hfkc.trans hbkc,
    hfc, hff, ha.of_writer hfrm hff⟩
  rw [hfkin, hbk]
  simp only [PredicateRequest.word, entryPredicateRequest, List.cons_append, List.nil_append]

end NearQuarticWires.StageMainMask
