import Proof.Quartic.StageLift.IndexSchema
import Proof.Quartic.StageLift.IndexModulus
import Proof.Quartic.StageLift.ListFields

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

/-- `lem:print`, paper/paper.tex: only normalized
index data is retained here; raw integer parsing uses the adjacent
marker store and never overwrites the original source stores. -/
def indexStore : Fin MM := 6
def indexMarkerStore : Fin MM := 7
def indexCountVar : Fin VV := 127

/-- `lem:print`, paper/paper.tex: read the actual
part, eight-pattern-bit list and prime before computing the recovery
modulus or streaming either signed target list. -/
def readPrintIndexHeader : St VV MM :=
  .seq (readFixedFields indexStore 1)
    (.seq (readListFields indexStore indexCountVar)
      (.seq (StageRecovery.readVariable indexPrimeVar) (.op (.wrM indexStore indexPrimeVar))))

/-- `lem:print`, paper/paper.tex: the actual small
header is consumed in its original codec and retained as ten scalar
records, with its real prime also physically loaded for p^e computation. -/
theorem readPrintIndexHeader_spec {B1 B2 : ℕ} (C : Ctx) (r : Greedy.PrintRequest B1 B2)
    (rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = printIndexHeader r ++ rest)
    (hW : 6 ≤ C.Wd) (hprime : natBitLength r.prime + 2 ≤ C.Wd)
    (hcursor : a.rc indexStore = (a.ram indexStore).length) :
    Hs C readPrintIndexHeader a (30 * natBitLength r.prime + 900) (fun b =>
      b.env indexPrimeVar = r.prime ∧
      b.ram indexStore = a.ram indexStore ++
        ([r.sign.toNat] ++ (List.ofFn r.pattern).map Bool.toNat ++ [r.prime]) ∧
      b.rc indexStore = a.rc indexStore + 10 ∧
      b.ip = a.ip + (printIndexHeader r).length ∧
      (∀ other, other ≠ indexStore → b.ram other = a.ram other ∧ b.rc other = a.rc other) ∧
      (b.out, b.kin, b.kout, b.kc) = (a.out, a.kin, a.kout, a.kc) ∧ Cst b ∧
      Fr a b (indexPrimeVar :: indexCountVar :: fieldIndex :: rdNatT)) := by
  let patterns := (List.ofFn r.pattern).map Bool.toNat
  have hpatlen : patterns.length = 8 := print_pattern_length r
  have h8 : natBitLength 8 = 4 := by decide
  have hpatwidth : natBitLength patterns.length + 2 ≤ C.Wd := by
    rw [hpatlen, h8]
    exact hW
  have hpatfit : patterns.length < 2 ^ C.Wd := by
    rw [hpatlen]
    have hpow : 2 ^ 6 ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by decide) hW
    exact lt_of_lt_of_le (by decide : 8 < 2 ^ 6) hpow
  have hsign : natBitLength r.sign.toNat = 1 := by cases r.sign <;> decide
  have hpattern : ∀ v ∈ patterns, natBitLength v ≤ 1 := by
    intro v hv
    obtain ⟨bit, _hbit, rfl⟩ := List.mem_map.mp hv
    cases bit <;> decide
  have hinput : C.inp.drop a.ip = natWord r.sign.toNat ++
      (listWord natWord patterns ++ natWord r.prime ++ rest) := by
    simpa only [printIndexHeader, patterns, List.append_assoc] using hin
  have hs := readFixedFields_spec C indexStore [r.sign.toNat]
    (listWord natWord patterns ++ natWord r.prime ++ rest) a hc (by simpa using hinput)
    (by
      intro v hv
      simp only [List.mem_singleton] at hv
      subst v
      rw [hsign]
      omega) hcursor
  simp only [List.map_singleton, List.sum_singleton, List.length_singleton, hsign] at hs
  unfold readPrintIndexHeader
  refine (Hs.seq (t1 := 65) (t2 := 30 * natBitLength r.prime + 744) hs
    fun b ⟨hbi, hbr, hbrc, hbo, hbsh, hbc, hbf⟩ => ?_).mono (by omega) (fun _ h => h)
  have hbin : C.inp.drop b.ip = listWord natWord patterns ++ natWord r.prime ++ rest := by
    rw [hbi, ← List.drop_drop, hinput]
    simp only [List.flatMap_singleton, List.drop_left]
  have hbcursor : b.rc indexStore = (b.ram indexStore).length := by
    rw [hbr, hbrc, List.length_append, List.length_singleton, hcursor]
  have hp := readListFields_spec C indexStore indexCountVar (by decide) (by decide) patterns 1
    (natWord r.prime ++ rest) b hbc (by simpa only [List.append_assoc] using hbin) hpattern (by omega)
    hpatwidth hpatfit hbcursor
  rw [hpatlen] at hp
  rw [h8] at hp
  refine (Hs.seq (t1 := 709) (t2 := 30 * natBitLength r.prime + 34) hp
    fun d ⟨_hdn, hdi, hdr, hdrc, hdo, hdsh, hdc, hdf⟩ => ?_).mono (by omega) (fun _ h => h)
  have hdin : C.inp.drop d.ip = natWord r.prime ++ rest := by
    rw [hdi, ← List.drop_drop, hbin, List.append_assoc, List.drop_left]
  refine Hs.seq (t1 := 30 * natBitLength r.prime + 32) (t2 := 1)
    (StageRecovery.readVariable_spec C d hdc indexPrimeVar (by decide) (by decide)
      r.prime rest hdin hprime) fun e ⟨hep, hei, herest, hec, hef⟩ => ?_
  have heram : e.ram = d.ram := congrArg (fun t => t.2.1) herest
  have herc : e.rc = d.rc := congrArg (fun t => t.2.2.1) herest
  have hesh : (e.out, e.kin, e.kout, e.kc) = (d.out, d.kin, d.kout, d.kc) :=
    congrArg (fun t => (t.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2)) herest
  have hecursor : e.rc indexStore = (e.ram indexStore).length := by
    rw [herc, heram, hdr, hdrc, List.length_append, hpatlen]
    exact hbcursor ▸ rfl
  refine (hs_wrM C indexStore indexPrimeVar e hecursor.le).mono le_rfl ?_
  rintro f rfl
  refine ⟨hep, ?_, ?_, ?_, ?_, hesh.trans (hdsh.trans hbsh),
    ⟨hec.z, hec.one, hec.two⟩, ?_⟩
  · simp only [DS.put, Function.update_self]
    rw [putAt, if_neg (by omega), hep, heram, hdr, hbr]
    simp only [List.append_assoc, patterns]
  · simp only [DS.put, Function.update_self, herc, hdrc, hbrc]
  · change e.ip = _
    rw [hei, hdi, hbi, printIndexHeader]
    simp only [List.flatMap_singleton, List.length_append, patterns]
    omega
  · intro other ho
    obtain ⟨hr₁, hc₁⟩ := hdo other ho
    obtain ⟨hr₂, hc₂⟩ := hbo other ho
    simpa only [DS.put, Function.update_of_ne ho, heram, herc] using
      And.intro (hr₁.trans hr₂) (hc₁.trans hc₂)
  · exact (hbf.weaken (by intro x hx; simp only [List.mem_cons]; tauto)).trans
      ((hdf.weaken (fun _ hx => List.mem_cons_of_mem _ hx)).trans
        (hef.weaken (by intro x hx; simp only [List.mem_cons] at hx ⊢; tauto)))

end NearQuarticWires.StageLift
