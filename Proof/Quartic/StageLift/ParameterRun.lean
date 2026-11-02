import Proof.Quartic.StageLift.ParameterReader

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

/-- `sec:params` and `lem:print`, paper/paper.tex: the actual whole parameter-word decoder reaches the
arbitrary following suffix and retains all scalar, prime and factor
fields in their canonical stores. -/
theorem readParameters_cursor_spec (C : Ctx) (p : Cells.Parameters) (B : ℕ)
    (rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = Program.parametersWord p ++ rest)
    (hwidth : ∀ value ∈ parameterHeadFields p ++ p.primes.sort (· ≤ ·) ++
      parameterTailFields p ++ p.factors, natBitLength value ≤ B)
    (hB : B + 2 ≤ C.Wd)
    (hcounts : p.primes.card < 2 ^ C.Wd ∧ p.factors.length < 2 ^ C.Wd)
    (hempty : ∀ store ∈ [parameterStore, primeStore, factorStore],
      a.ram store = [] ∧ a.rc store = 0) :
    Hs C readParameters a (parameterReadCost p B) (fun b =>
      (b.ip = a.ip + (Program.parametersWord p).length ∧
      b.ram parameterStore = parameterScalars p ∧
      b.ram primeStore = p.primes.sort (· ≤ ·) ∧ b.ram factorStore = p.factors ∧
      b.env primeCountVar = p.primes.card ∧ b.env factorCountVar = p.factors.length ∧
      (b.out, b.kin, b.kout, b.kc) = (a.out, a.kin, a.kout, a.kc) ∧ Cst b ∧
      Fr a b (primeCountVar :: factorCountVar :: fieldIndex :: rdNatT)) ∧
      b.rc parameterStore = 46 ∧ b.rc primeStore = p.primes.card ∧
      b.rc factorStore = p.factors.length) := by
  let H := parameterHeadScalars p
  let T := parameterTailScalars p
  let P := p.primes.sort (· ≤ ·)
  have hHlen : H.length = 37 := parameterHeadScalars_length p
  have hTlen : T.length = 9 := parameterTailScalars_length p
  have hPlen : P.length = p.primes.card := by simp [P]
  have hHwidth : ∀ v ∈ H, natBitLength v + 2 ≤ C.Wd := by
    intro v hv
    apply (Nat.add_le_add_right (hwidth v ?_) 2).trans hB
    simp only [parameterHeadFields, List.mem_append, List.mem_singleton]
    exact Or.inl (Or.inl (Or.inl (Or.inl hv)))
  have hTwidth : ∀ v ∈ T, natBitLength v + 2 ≤ C.Wd := by
    intro v hv
    apply (Nat.add_le_add_right (hwidth v ?_) 2).trans hB
    simp only [parameterTailFields, List.mem_append, List.mem_singleton]
    tauto
  have hPwidth : ∀ v ∈ P, natBitLength v ≤ B := by
    intro v hv
    exact hwidth v (by simp only [List.mem_append]; tauto)
  have hFwidth : ∀ v ∈ p.factors, natBitLength v ≤ B := by
    intro v hv
    exact hwidth v (by simp only [List.mem_append]; tauto)
  have hpbits : natBitLength P.length + 2 ≤ C.Wd := by
    rw [hPlen]
    apply (Nat.add_le_add_right (hwidth p.primes.card ?_) 2).trans hB
    simp [parameterHeadFields]
  have hfbits : natBitLength p.factors.length + 2 ≤ C.Wd := by
    apply (Nat.add_le_add_right (hwidth p.factors.length ?_) 2).trans hB
    simp [parameterTailFields]
  have hstart : C.inp.drop a.ip = H.flatMap natWord ++ listWord natWord P ++
      T.flatMap natWord ++ listWord natWord p.factors ++ rest := by
    rw [hin, parametersWord_block_layout]
  have eH := readFixedFields_spec C parameterStore H
    (listWord natWord P ++ T.flatMap natWord ++ listWord natWord p.factors ++ rest) a hc
    (by simpa only [List.append_assoc] using hstart) hHwidth (by
      obtain ⟨hr, hc'⟩ := hempty parameterStore (by simp)
      rw [hr, hc']; rfl)
  rw [hHlen] at eH
  unfold readParameters parameterReadCost
  refine (Hs.seq (t2 :=
      (30 * natBitLength p.primes.card + p.primes.card * (30 * B + 39) + 37) +
      ((30 * (T.map natBitLength).sum + 34 * 9 + 1) +
        (30 * natBitLength p.factors.length + p.factors.length * (30 * B + 39) + 37) + 1) + 1)
    eH fun b ⟨hbi, hbr, hbrc, hbother, hbsh, hbc, hbf⟩ => ?_).mono
      (by dsimp only [H, T]; omega) (fun _ h => h)
  have hbr' : b.ram parameterStore = H := by rw [hbr, (hempty _ (by simp)).1]; rfl
  have hbrc' : b.rc parameterStore = 37 := by rw [hbrc, (hempty _ (by simp)).2]
  have hbin : C.inp.drop b.ip = listWord natWord P ++ T.flatMap natWord ++
      listWord natWord p.factors ++ rest := by
    rw [hbi, ← List.drop_drop, hstart]
    simp only [List.append_assoc, List.drop_left]
  have eP := readListFields_spec C primeStore primeCountVar (by decide) (by decide) P B
    (T.flatMap natWord ++ listWord natWord p.factors ++ rest) b hbc
    (by simpa only [List.append_assoc] using hbin) hPwidth hB hpbits (by rw [hPlen]; exact hcounts.1)
    (by obtain ⟨hr, hc'⟩ := hbother primeStore (by decide)
        rw [hc', hr, (hempty _ (by simp)).1, (hempty _ (by simp)).2]; rfl)
  rw [hPlen] at eP
  refine Hs.seq eP fun d ⟨hdn, hdi, hdr, hdrc, hdother, hdsh, hdc, hdf⟩ => ?_
  have hdr' : d.ram parameterStore = H := by rw [(hdother _ (by decide)).1, hbr']
  have hdrc' : d.rc parameterStore = 37 := by rw [(hdother _ (by decide)).2, hbrc']
  have hdP : d.ram primeStore = P := by
    rw [hdr, (hbother _ (by decide)).1, (hempty _ (by simp)).1]; rfl
  have hdin : C.inp.drop d.ip = T.flatMap natWord ++ listWord natWord p.factors ++ rest := by
    rw [hdi, ← List.drop_drop, hbin]
    simp only [List.append_assoc, List.drop_left]
  have eT := readFixedFields_spec C parameterStore T
    (listWord natWord p.factors ++ rest) d hdc
    (by simpa only [List.append_assoc] using hdin) hTwidth (by rw [hdr', hdrc', hHlen])
  rw [hTlen] at eT
  refine Hs.seq eT fun e ⟨hei, her, herc, heother, hesh, hec, hef⟩ => ?_
  have heF : e.ram factorStore = [] ∧ e.rc factorStore = 0 := by
    obtain ⟨hr1, hc1⟩ := heother factorStore (by decide)
    obtain ⟨hr2, hc2⟩ := hdother factorStore (by decide)
    obtain ⟨hr3, hc3⟩ := hbother factorStore (by decide)
    rw [hr1, hr2, hr3, hc1, hc2, hc3]
    exact hempty factorStore (by simp)
  have hein : C.inp.drop e.ip = listWord natWord p.factors ++ rest := by
    rw [hei, ← List.drop_drop, hdin]
    simp only [List.append_assoc, List.drop_left]
  refine (readListFields_spec C factorStore factorCountVar (by decide) (by decide) p.factors B
    rest e hec hein hFwidth hB hfbits hcounts.2 (by rw [heF.1, heF.2]; rfl)).mono le_rfl ?_
  rintro f ⟨hfn, hfi, hfr, _hfrc, hfother, hfsh, hfc, hff⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    refine ⟨?_, ?_, ?_, ?_, ?_, hfn, hfsh.trans (hesh.trans (hdsh.trans hbsh)), hfc, ?_⟩
    · rw [hfi, hei, hdi, hbi, parametersWord_block_layout]
      dsimp only [H, T, P]
      simp only [List.length_append]
      omega
    · rw [(hfother _ (by decide)).1, her, hdr']
      rfl
    · rw [(hfother _ (by decide)).1, (heother _ (by decide)).1, hdP]
    · rw [hfr, heF.1]; rfl
    · rw [hff primeCountVar (by decide), hef primeCountVar (by decide), hdn]
    · exact Fr.trans (hbf.weaken (by intro y hy; simp only [List.mem_cons]; tauto))
        (Fr.trans (hdf.weaken (by intro y hy; simp only [List.mem_cons] at hy ⊢; tauto))
          (Fr.trans (hef.weaken (by intro y hy; simp only [List.mem_cons]; tauto))
            (hff.weaken (by intro y hy; simp only [List.mem_cons] at hy ⊢; tauto))))
  · rw [(hfother _ (by decide)).2, herc, hdrc']
  · rw [(hfother _ (by decide)).2, (heother _ (by decide)).2, hdrc,
      (hbother _ (by decide)).2, (hempty _ (by simp)).2]
    omega
  · rw [_hfrc, heF.2]
    omega

/-- `sec:params` and `lem:print`, paper/paper.tex: the original parameter-reader interface follows from
the stronger cursor-preserving physical execution theorem. -/
theorem readParameters_spec (C : Ctx) (p : Cells.Parameters) (B : ℕ)
    (rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = Program.parametersWord p ++ rest)
    (hwidth : ∀ value ∈ parameterHeadFields p ++ p.primes.sort (· ≤ ·) ++
      parameterTailFields p ++ p.factors, natBitLength value ≤ B)
    (hB : B + 2 ≤ C.Wd)
    (hcounts : p.primes.card < 2 ^ C.Wd ∧ p.factors.length < 2 ^ C.Wd)
    (hempty : ∀ store ∈ [parameterStore, primeStore, factorStore],
      a.ram store = [] ∧ a.rc store = 0) :
    Hs C readParameters a (parameterReadCost p B) (fun b =>
      b.ip = a.ip + (Program.parametersWord p).length ∧
      b.ram parameterStore = parameterScalars p ∧
      b.ram primeStore = p.primes.sort (· ≤ ·) ∧ b.ram factorStore = p.factors ∧
      b.env primeCountVar = p.primes.card ∧ b.env factorCountVar = p.factors.length ∧
      (b.out, b.kin, b.kout, b.kc) = (a.out, a.kin, a.kout, a.kc) ∧ Cst b ∧
      Fr a b (primeCountVar :: factorCountVar :: fieldIndex :: rdNatT)) := by
  exact (readParameters_cursor_spec C p B rest a hc hin hwidth hB hcounts hempty).mono
    le_rfl (fun _ h => h.1)

end NearQuarticWires.StageLift
