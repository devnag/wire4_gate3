import Proof.Quartic.StageMain.CallSkipCore

/-!
# A counted scanner for nested call records

The polynomial reading bound in `prop:time`, paper/paper.tex, charges every record of each original circuit. This
loop consumes a literal list of encoded records without retaining the
payload or changing any record store.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.CallSkip

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells

variable {α : Type}

def skipLoop (index count : Fin VV) (body : St VV MM) : St VV MM :=
  .loop (.lt index count) (.seq body (.op (.inc index)))

theorem skipLoop_run (C : Ctx) (index count : Fin VV) (hneq : index ≠ count)
    (hconst : index ≠ vZ ∧ index ≠ v1 ∧ index ≠ v2)
    (hicounter : index ≠ lengthCounter)
    (body : St VV MM) (encode : α → List Bool) (xs : List α) (T : List (Fin VV))
    (hiT : index ∉ T) (hcT : count ∉ T) (t start : ℕ) (rest : List Bool)
    (a : DS VV MM) (hc : Cst a)
    (hi : a.env index = start) (hn : a.env count = start + xs.length)
    (hfit : start + xs.length < 2 ^ C.Wd)
    (hin : C.inp.drop a.ip = xs.flatMap encode ++ rest)
    (hcap : a.env lengthCounter + (xs.flatMap encode).length < 2 ^ C.Wd)
    (hbody : ∀ x ∈ xs, ∀ b, Cst b → ∀ tail,
      C.inp.drop b.ip = encode x ++ tail →
      b.env lengthCounter + (encode x).length < 2 ^ C.Wd →
      Hs C body b t (fun d => Scanned b d (encode x).length T)) :
    Hs C (skipLoop index count body) a (xs.length * (t + 4) + 2) (fun b =>
      Scanned a b (xs.flatMap encode).length (index :: T) ∧
      b.env index = start + xs.length) := by
  induction xs generalizing start a with
  | nil =>
    have he : (Cnd.lt index count).eval a = false := by simp [Cnd.eval, hi, hn]
    refine ⟨a, 2, Ex.loopF hneq he, by simp, ?_⟩
    exact ⟨⟨by simp, rfl, hc, Fr.refl _ _, by simp⟩, by simpa using hi⟩
  | cons x xs ih =>
    have he : (Cnd.lt index count).eval a = true := by simp [Cnd.eval, hi, hn]
    have hxinput : C.inp.drop a.ip = encode x ++ (xs.flatMap encode ++ rest) := by
      simpa only [List.flatMap_cons, List.append_assoc] using hin
    obtain ⟨b, n, hb, hnt, hbs⟩ := hbody x (by simp) a hc _ hxinput (by
      simp only [List.flatMap_cons, List.length_append] at hcap
      omega)
    have hbi : b.env index = start := (hbs.registers index hiT).trans hi
    have hbn : b.env count = start + (x :: xs).length := (hbs.registers count hcT).trans hn
    have hbfit : b.env index + 1 < 2 ^ C.Wd := by
      rw [hbi]
      simp only [List.length_cons] at hfit
      omega
    let b1 := b.set index (start + 1)
    have hinc : Ex C (.op (.inc index)) b b1 1 := by
      simpa only [b1, hbi] using (Ex.op (OpEx.inc index b hbfit))
    have hfr1 : Fr b b1 [index] := Fr.set b _ (by simp)
    have hbc : Cst b1 := Cst.of_fr hbs.constants hfr1 (by
      simp only [List.mem_singleton]
      exact ⟨hconst.1.symm, hconst.2.1.symm, hconst.2.2.symm⟩)
    have h1count : b1.env count = start + 1 + xs.length := by
      rw [DS.set_env_ne _ _ hneq.symm, hbn]
      simp only [List.length_cons]
      omega
    have h1input : C.inp.drop b1.ip = xs.flatMap encode ++ rest := hbs.tail hxinput
    obtain ⟨d, k, hd, hkt, hds, hdi⟩ := ih (start + 1) b1 hbc (by simp [b1]) h1count
      (by simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfit)
      h1input (by
        dsimp only [b1]
        rw [DS.set_env_ne _ _ hicounter.symm, hbs.bytes]
        simp only [List.flatMap_cons, List.length_append] at hcap
        omega) (fun y hy => hbody y (by simp [hy]))
    refine ⟨d, (n + 1 + 1) + k + 2, Ex.loopT hneq he (Ex.seq hb hinc) hd, ?_, ?_⟩
    · simp only [List.length_cons]
      nlinarith
    · have haf : Fr a b1 (index :: T) :=
        (hbs.registers.weaken (fun _ hx => List.mem_cons_of_mem _ hx)).trans
          (hfr1.weaken (by simp))
      refine ⟨⟨?_, hds.unchanged.trans hbs.unchanged, hds.constants,
        haf.trans hds.registers, ?_⟩, ?_⟩
      · rw [hds.pos]
        change b.ip + (xs.flatMap encode).length = _
        rw [hbs.pos]
        simp only [List.flatMap_cons, List.length_append]
        omega
      · rw [hds.bytes]
        dsimp only [b1]
        rw [DS.set_env_ne _ _ hicounter.symm, hbs.bytes]
        simp only [List.flatMap_cons, List.length_append]
        omega
      · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hdi

end NearQuarticWires.StageMain.CallSkip
