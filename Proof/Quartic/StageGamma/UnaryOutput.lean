import Proof.Quartic.StageGamma.Emit

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageGamma

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells

/-- `cor:conditional`, paper/paper.tex: emit one
marked true bit of the unary field-setup input. -/
def unaryPair : St VV MM := .seq (.op (.emit true)) (.op (.emit true))

/-- `cor:conditional`, paper/paper.tex: the unary
degree is physically written as a framed output word. -/
def unaryOutput (count : Fin VV) : St VV MM :=
  .seq (forS emitIndex count unaryPair) (.op (.emit false))

/-- `cor:conditional`, paper/paper.tex: marking a
unary word is a concatenation of the actual two-bit marker blocks. -/
theorem frame_replicate_true (n : ℕ) :
    frame (List.replicate n true) = bitBlocks [true, true] n ++ [false] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, frame, ih]
    simp [bitBlocks, List.replicate_succ]

/-- `cor:conditional` and `prop:time`, paper/paper.tex: the original decoded field degree is converted to a unary
setup word by actual output operations in linear time. -/
theorem unaryOutput_spec (C : Ctx) (count : Fin VV) (hci : emitIndex ≠ count)
    (a : DS VV MM) (N : ℕ) (hcount : a.env count = N) (hN : N < 2 ^ C.Wd) :
    Hs C (unaryOutput count) a (7 * N + 6) (fun b =>
      b.out = a.out ++ frame (List.replicate N true) ∧
      b.ip = a.ip ∧ b.kin = a.kin) := by
  let I : ℕ → DS VV MM → Prop := fun k b =>
    b.out = a.out ++ bitBlocks [true, true] k ∧ b.ip = a.ip ∧ b.kin = a.kin
  have hi : ∀ k b v, I k b → I k (b.set emitIndex v) := by
    intro k b v hb
    exact hb
  have h0 : I 0 a := ⟨by simp [bitBlocks], rfl, rfl⟩
  have hl := forS_spec' emitIndex count hci unaryPair a N hN I 3 hi h0 hcount (by
    intro k hk b ⟨hb, hip, hkin⟩ hki hcn
    refine Hs.mono (Hs.seq (t2 := 1)
      (R2 := fun d => d = { b with out := b.out ++ [true, true] })
      (hs_emit C true b) (fun e he => ?_)) le_rfl ?_
    · subst he
      simpa [List.append_assoc] using
        hs_emit C true ({ b with out := b.out ++ [true] } : DS VV MM)
    · rintro e rfl
      refine ⟨⟨?_, hip, hkin⟩, hki, hcn⟩
      simp [hb, bitBlocks_succ, List.append_assoc])
  refine Hs.mono (Hs.seq (t2 := 1) hl (fun b hb => ?_)) (by omega) (fun _ h => h)
  obtain ⟨⟨hout, hip, hkin⟩, _, _⟩ := hb
  refine Hs.mono (hs_emit C false b) le_rfl ?_
  rintro e rfl
  exact ⟨by simpa [frame_replicate_true, List.append_assoc] using congrArg (fun w => w ++ [false]) hout,
    hip, hkin⟩

end NearQuarticWires.StageGamma
