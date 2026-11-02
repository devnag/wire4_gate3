import Proof.Quartic.StageMain.CallSkipMeasure

/-!
# Scanning self-delimiting fields of the original call

The ordinary implementation in `prop:time`, paper/paper.tex, reads the original circuit description in polynomial
time. These field scanners advance only the input cursor and their
explicit arithmetic scratch, preserving every retained record store.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.CallSkip

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

structure Scanned (a b : DS VV MM) (length : ℕ) (scratch : List (Fin VV)) : Prop where
  pos : b.ip = a.ip + length
  unchanged : (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) =
    (a.out, a.ram, a.rc, a.kin, a.kout, a.kc)
  constants : Cst b
  registers : Fr a b scratch
  bytes : b.env lengthCounter = a.env lengthCounter + length

theorem Scanned.then_scanned {a b d : DS VV MM} {L K : ℕ} {T U : List (Fin VV)}
    (h : Scanned a b L T) (g : Scanned b d K U) : Scanned a d (L + K) (T ++ U) := by
  refine ⟨by rw [g.pos, h.pos]; omega, g.unchanged.trans h.unchanged, g.constants, ?_, ?_⟩
  · exact (h.registers.weaken (fun _ hx => List.mem_append_left _ hx)).trans
      (g.registers.weaken (fun _ hx => List.mem_append_right _ hx))
  · rw [g.bytes, h.bytes]; omega

theorem Scanned.tail {C : Ctx} {a b : DS VV MM} {word rest : List Bool} {T : List (Fin VV)}
    (h : Scanned a b word.length T) (hin : C.inp.drop a.ip = word ++ rest) :
    C.inp.drop b.ip = rest := by
  rw [h.pos, ← List.drop_drop, hin, List.drop_left]

theorem skipNat_run (C : Ctx) (a : DS VV MM) (hc : Cst a) (v : ℕ) (rest : List Bool)
    (hin : C.inp.drop a.ip = natWord v ++ rest) (hW : natBitLength v + 2 ≤ C.Wd)
    (hcap : a.env lengthCounter + (natWord v).length < 2 ^ C.Wd) :
    Hs C scanNat a (30 * natBitLength v + 36)
      (fun b => Scanned a b (natWord v).length atomScratch) := by
  refine (scanNat_read_run C a hc v rest hin hW hcap).mono le_rfl ?_
  intro b ⟨_, _, hp, hu, hbc, hf, hlen⟩
  exact ⟨hp, hu, hbc, hf, hlen⟩

theorem skipSeq_run (C : Ctx) (P Q : St VV MM) (a : DS VV MM)
    (x y : List Bool) (T U : List (Fin VV)) (t u : ℕ)
    (hP : Hs C P a t (fun b => Scanned a b x.length T))
    (hQ : ∀ b, Scanned a b x.length T → Hs C Q b u (fun d => Scanned b d y.length U)) :
    Hs C (.seq P Q) a (t + u + 1) (fun d => Scanned a d (x ++ y).length (T ++ U)) := by
  refine Hs.seq hP ?_
  intro b hb
  refine (hQ b hb).mono le_rfl ?_
  intro d hd
  simpa only [List.length_append] using hb.then_scanned hd

end NearQuarticWires.StageMain.CallSkip
