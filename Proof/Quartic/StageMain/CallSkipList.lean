import Proof.Quartic.StageMain.CallSkipLoop

/-!
# Reading the length of each original record list

`prop:time`, paper/paper.tex: list lengths are read from
self-delimiting binary fields before the counted traversal. Neither
list lengths nor decoded record values are supplied to the machine.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.CallSkip

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

variable {α : Type}

def skipList (index count : Fin VV) (body : St VV MM) : St VV MM :=
  .seq scanNat (.seq (.op (.copy count t3))
    (.seq (.op (.zero index)) (skipLoop index count body)))

def listScratch (index count : Fin VV) (T : List (Fin VV)) : List (Fin VV) :=
  atomScratch ++ count :: index :: T

theorem skipList_run (C : Ctx) (index count : Fin VV) (hneq : index ≠ count)
    (hiSafe : index ∉ [vZ, v1, v2]) (hcSafe : count ∉ [vZ, v1, v2])
    (hiCounter : index ≠ lengthCounter) (hcCounter : count ≠ lengthCounter)
    (hcRead : count ≠ t3) (body : St VV MM) (encode : α → List Bool)
    (xs : List α) (T : List (Fin VV)) (hiT : index ∉ T) (hcT : count ∉ T)
    (t : ℕ) (rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop a.ip = listWord encode xs ++ rest)
    (hW : natBitLength xs.length + 2 ≤ C.Wd) (hfit : xs.length < 2 ^ C.Wd)
    (hcap : a.env lengthCounter + (listWord encode xs).length < 2 ^ C.Wd)
    (hbody : ∀ x ∈ xs, ∀ b, Cst b → ∀ tail,
      C.inp.drop b.ip = encode x ++ tail →
      b.env lengthCounter + (encode x).length < 2 ^ C.Wd →
      Hs C body b t (fun d => Scanned b d (encode x).length T)) :
    Hs C (skipList index count body) a
      (30 * natBitLength xs.length + xs.length * (t + 4) + 43)
      (fun b => Scanned a b (listWord encode xs).length (listScratch index count T)) := by
  unfold skipList
  refine Hs.mono (Hs.seq (t1 := 30 * natBitLength xs.length + 36)
    (t2 := 1 + (1 + (xs.length * (t + 4) + 2) + 1) + 1)
    (scanNat_read_run C a hc xs.length (xs.flatMap encode ++ rest)
      (by simpa only [listWord, List.append_assoc] using hin) hW
      (by simp only [listWord, List.length_append] at hcap; omega)) ?_) (by omega) (fun _ h => h)
  intro b ⟨hbn, _, hbpos, hbrest, hbc, hbfr, hblen⟩
  refine Hs.seq (t1 := 1) (t2 := 1 + (xs.length * (t + 4) + 2) + 1)
    (hs_copy C count t3 b hcRead) ?_
  rintro d rfl
  refine Hs.seq (t1 := 1) (t2 := xs.length * (t + 4) + 2) (hs_zero C index _) ?_
  rintro d rfl
  let d := (b.set count (b.env t3)).set index 0
  have hfd : Fr b d [count, index] :=
    (Fr.set b _ (by simp)).trans (Fr.set _ _ (by simp))
  have hdc : Cst d := Cst.of_fr hbc hfd (by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hiSafe hcSafe ⊢
    exact ⟨⟨Ne.symm (hcSafe.1), Ne.symm (hiSafe.1)⟩,
      ⟨Ne.symm (hcSafe.2.1), Ne.symm (hiSafe.2.1)⟩, ⟨Ne.symm (hcSafe.2.2), Ne.symm (hiSafe.2.2)⟩⟩)
  have hdinput : C.inp.drop d.ip = xs.flatMap encode ++ rest := by
    change C.inp.drop b.ip = _
    rw [hbpos, ← List.drop_drop, hin, listWord, List.append_assoc, List.drop_left]
  have hic : index ≠ vZ ∧ index ≠ v1 ∧ index ≠ v2 := by simpa using hiSafe
  refine (skipLoop_run C index count hneq hic hiCounter body encode xs T hiT hcT t 0 rest d hdc
    (by simp [d]) (by simp [d, hneq.symm, hbn]) (by simpa using hfit) hdinput
    (by
      dsimp only [d]
      rw [DS.set_env_ne _ _ hiCounter.symm, DS.set_env_ne _ _ hcCounter.symm, hblen]
      simp only [listWord, List.length_append] at hcap
      omega) hbody).mono le_rfl ?_
  intro e ⟨hes, _⟩
  refine ⟨?_, hes.unchanged.trans hbrest, hes.constants, ?_, ?_⟩
  · rw [hes.pos]
    change b.ip + (xs.flatMap encode).length = _
    rw [hbpos]
    simp only [listWord, List.length_append]
    omega
  · have hf : Fr a d (listScratch index count T) :=
      (hbfr.weaken (fun _ hx => List.mem_append_left _ hx)).trans
        (hfd.weaken (by intro y hy; simp only [List.mem_append,
          List.mem_cons, List.not_mem_nil, or_false] at hy ⊢; tauto))
    exact hf.trans (hes.registers.weaken (by
      intro y hy
      exact List.mem_append_right _ (List.mem_cons_of_mem _ hy)))
  · rw [hes.bytes]
    dsimp only [d]
    rw [DS.set_env_ne _ _ hiCounter.symm, DS.set_env_ne _ _ hcCounter.symm, hblen]
    simp only [listWord, List.length_append]
    omega

end NearQuarticWires.StageMain.CallSkip
