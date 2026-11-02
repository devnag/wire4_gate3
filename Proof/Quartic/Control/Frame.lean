import Proof.Quartic.Control.Round

/-!
# Streams a program never touches

Paper: `prop:time` and the word-function model of `thm:counter`, paper/paper.tex: the
counter program writes its output word exactly on its output tape.

The correctness statements of the call and the cleanup describe the states only up to reading (`SimW`): a stream may
carry trailing blanks. The output tape of a word function must hold its word exactly, so the output stream is kept
out of every phase but the last one. `WMX.Avoids i P` says that no instruction of `P` writes stream `i` or moves its
head, and no machine is docked on it; then every run of `P` leaves the contents and the head of `i` exactly as they
were (`WXExec.avoids`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Control

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms

variable {ns nr : ℕ}

/-- No instruction of the register program writes the stream `i` or moves its head. -/
def WM.Avoids (i : Fin (ns + 1)) : WM ns nr → Prop
  | .skip => True
  | .inc _ => True
  | .dec _ => True
  | .fwd j => j ≠ i
  | .bwd j => j ≠ i
  | .wr j _ => j ≠ i
  | .setc _ => True
  | .seq P Q => WM.Avoids i P ∧ WM.Avoids i Q
  | .ifr _ P Q => WM.Avoids i P ∧ WM.Avoids i Q
  | .ifs _ P Q => WM.Avoids i P ∧ WM.Avoids i Q
  | .whr _ P => WM.Avoids i P
  | .whs _ P => WM.Avoids i P

/-- No instruction of the word program writes the stream `i` or moves its head, and no machine is docked on it. -/
def WMX.Avoids (i : Fin (ns + 1)) : WMX ns nr → Prop
  | .wm P => WM.Avoids i P
  | .mach _ tmap => ∀ j, tmap j ≠ i
  | .seq P Q => WMX.Avoids i P ∧ WMX.Avoids i Q
  | .ifr _ P Q => WMX.Avoids i P ∧ WMX.Avoids i Q
  | .ifs _ P Q => WMX.Avoids i P ∧ WMX.Avoids i Q
  | .whr _ P => WMX.Avoids i P
  | .whs _ P => WMX.Avoids i P

theorem WExec.avoids {cap : ℕ} {i : Fin (ns + 1)} {P : WM ns nr} {σ τ : WState ns nr} {n : ℕ}
    (h : WExec cap P σ τ n) (hP : WM.Avoids i P) : τ.st i = σ.st i ∧ τ.sh i = σ.sh i := by
  induction h with
  | skip => exact ⟨rfl, rfl⟩
  | inc => exact ⟨rfl, rfl⟩
  | dec => exact ⟨rfl, rfl⟩
  | fwd j σ =>
    simp only [WM.Avoids] at hP
    exact ⟨rfl, by simp [Function.update_of_ne (Ne.symm hP)]⟩
  | bwd j σ =>
    simp only [WM.Avoids] at hP
    exact ⟨rfl, by simp [Function.update_of_ne (Ne.symm hP)]⟩
  | wr j b σ =>
    simp only [WM.Avoids] at hP
    exact ⟨by simp [Function.update_of_ne (Ne.symm hP)], rfl⟩
  | setc => exact ⟨rfl, rfl⟩
  | seq _ _ ih1 ih2 =>
    obtain ⟨h1, h2⟩ := hP
    exact ⟨(ih2 h2).1.trans (ih1 h1).1, (ih2 h2).2.trans (ih1 h1).2⟩
  | ifrT _ _ ih => exact ih hP.1
  | ifrF _ _ ih => exact ih hP.2
  | ifsT _ _ ih => exact ih hP.1
  | ifsF _ _ ih => exact ih hP.2
  | whrF => exact ⟨rfl, rfl⟩
  | whrT _ _ _ ih1 ih2 => exact ⟨(ih2 hP).1.trans (ih1 hP).1, (ih2 hP).2.trans (ih1 hP).2⟩
  | whsF => exact ⟨rfl, rfl⟩
  | whsT _ _ _ ih1 ih2 => exact ⟨(ih2 hP).1.trans (ih1 hP).1, (ih2 hP).2.trans (ih1 hP).2⟩
  | mono _ _ ih => exact ih hP

/-- **A program that avoids a stream leaves it exactly as it was.** -/
theorem WXExec.avoids {cap : ℕ} {i : Fin (ns + 1)} {P : WMX ns nr} {σ τ : WState ns nr} {n : ℕ}
    (h : WXExec cap P σ τ n) (hP : WMX.Avoids i P) : τ.st i = σ.st i ∧ τ.sh i = σ.sh i := by
  induction h with
  | wm h => exact WExec.avoids h hP
  | mach σ hinj _ =>
    exact ⟨updS_st_other _ _ _ _ i hP, updS_sh_other _ _ _ _ i hP⟩
  | seq _ _ ih1 ih2 =>
    obtain ⟨h1, h2⟩ := hP
    exact ⟨(ih2 h2).1.trans (ih1 h1).1, (ih2 h2).2.trans (ih1 h1).2⟩
  | ifrT _ _ ih => exact ih hP.1
  | ifrF _ _ ih => exact ih hP.2
  | ifsT _ _ ih => exact ih hP.1
  | ifsF _ _ ih => exact ih hP.2
  | whrF => exact ⟨rfl, rfl⟩
  | whrT _ _ _ ih1 ih2 => exact ⟨(ih2 hP).1.trans (ih1 hP).1, (ih2 hP).2.trans (ih1 hP).2⟩
  | whsF => exact ⟨rfl, rfl⟩
  | whsT _ _ _ ih1 ih2 => exact ⟨(ih2 hP).1.trans (ih1 hP).1, (ih2 hP).2.trans (ih1 hP).2⟩
  | mono _ _ ih => exact ih hP

theorem addCases_val {n m : ℕ} (f : Fin n → Fin m) (g : Fin 1 → Fin m) (P : ℕ → Prop) (hf : ∀ j, P (f j).val)
    (hg : P (g 0).val) : ∀ j, P (Fin.addCases (motive := fun _ => Fin m) f g j).val := by
  intro j
  refine Fin.addCases (fun j' => ?_) (fun j' => ?_) j
  · simp only [Fin.addCases_left]; exact hf j'
  · simp only [Fin.addCases_right]; rw [Fin.fin_one_eq_zero j']; exact hg

/-- The round avoids the output stream. -/
theorem roundP_avoids (p : Program) : WMX.Avoids (sOUT p.tapeCount) (roundP p) := by
  simp [WMX.Avoids, WM.Avoids, roundP, writeChild, copyLoop, preEmit, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.emitPair, emitC, WM.fwdC,
    NearCubicGates.Close.Codec.emitScanned, NearCubicGates.Close.Codec.rewindLoop, WM.rewind, callP, cleanP,
    eraseP, WMX.machZ, NearCubicGates.Close.WorkerArith.guardP, NearCubicGates.Close.WorkerArith.tallyP,
    NearCubicGates.Close.WorkerArith.clearSelfP, NearCubicGates.Close.WorkerArith.twoOnes, BinW.width,
    BinW.widthW, BinW.widthLoop, BinW.backLoop, ltInt, ltNat, prefixBody, bitBody, clrR, setR, bothFwd, bothBwd,
    fw2, bw2, appendBit, walkLoop, WMX.fwd, WMX.bwd, WMX.wr, WMX.inc, WMX.dec, WMX.skip, Site.input, Site.swept,
    siteA, siteB, sOUT, sIN, sP, sL, sTA, sGA, sTB, sGB, bankA, bankB, Fin.ext_iff]
  and_intros
  all_goals (repeat' apply addCases_val (P := fun v => ¬ v = 1))
  all_goals first | omega | (intro j; simp [bankA, bankB]; omega) | simp

end NearQuarticWires.Control
