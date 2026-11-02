import Proof.Gates.Expand.PolyTabPack

/-!
# Sequential composition of word functions

Paper: `prop:time`, paper/paper.tex: the counter runs parameter preparation and Steps 1–5 of
`sec:algorithm` one after the other, and its running time is the sum of the costs of the steps.

`WordFunction.pipe f g` runs `f` and then `g` on the output of `f`. The handoff is exact: `f` writes the framed word
`frame (m r)` on its output tape, which is precisely the input tape that `g` expects, so the first tape of `g` is
the output tape of `f` and no copying is needed. The two programs run on disjoint banks of streams of one `WMX`
layout, each docked by `WMX.machZ` (imported from `Proof.Gates.WordPrograms.WMX`), and the program is packaged by
`Expand.PolyTab.wordFunction_of_ideal`. The cost is `4 b_f + 4 b_g + 12`.
-/

set_option autoImplicit false

namespace NearQuarticWires.Program

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.Expand.PolyTab (idealStart wordFunction_of_ideal)

section Layout

variable (tf tg : ℕ)

/-- The stream count of the two-bank layout: `t_f` streams for the first program, `t_g` for the second (the slot of
its first tape stays unused), and two rulers. -/
abbrev pipeStreams : ℕ := tf + tg + 1

/-- Tape `j` of the first program is stream `j`. -/
def firstMap (j : Fin tf) : Fin (pipeStreams tf tg + 1) := ⟨j.val, by have := j.isLt; unfold pipeStreams; omega⟩

/-- Tape `0` of the second program is the output stream `o` of the first; tape `j ≠ 0` is stream `t_f + j`. -/
def secondMap (o : Fin tf) (j : Fin tg) : Fin (pipeStreams tf tg + 1) :=
  if j.val = 0 then firstMap tf tg o else ⟨tf + j.val, by have := j.isLt; unfold pipeStreams; omega⟩

/-- The ruler of the first program. -/
def firstRuler : Fin (pipeStreams tf tg + 1) := ⟨tf + tg, by unfold pipeStreams; omega⟩

/-- The ruler of the second program. -/
def secondRuler : Fin (pipeStreams tf tg + 1) := ⟨tf + tg + 1, by unfold pipeStreams; omega⟩

theorem firstMap_val (j : Fin tf) : (firstMap tf tg j).val = j.val := rfl

theorem secondMap_zero (o : Fin tf) (j : Fin tg) (h : j.val = 0) : secondMap tf tg o j = firstMap tf tg o := by
  simp [secondMap, h]

theorem secondMap_val (o : Fin tf) (j : Fin tg) (h : j.val ≠ 0) : (secondMap tf tg o j).val = tf + j.val := by
  simp [secondMap, h]

theorem firstMap_injective : Function.Injective (firstMap tf tg) := by
  intro a b h
  exact Fin.ext (by simpa [firstMap] using congrArg Fin.val h)

theorem secondMap_injective (o : Fin tf) : Function.Injective (secondMap tf tg o) := by
  intro a b h
  have ho := o.isLt
  apply Fin.ext
  by_cases ha : a.val = 0 <;> by_cases hb : b.val = 0
  · omega
  · have h1 := congrArg Fin.val h
    rw [secondMap_zero tf tg o a ha, secondMap_val tf tg o b hb, firstMap_val] at h1
    omega
  · have h1 := congrArg Fin.val h
    rw [secondMap_val tf tg o a ha, secondMap_zero tf tg o b hb, firstMap_val] at h1
    omega
  · have h1 := congrArg Fin.val h
    rw [secondMap_val tf tg o a ha, secondMap_val tf tg o b hb] at h1
    omega

theorem firstMap_ne_firstRuler (j : Fin tf) : firstMap tf tg j ≠ firstRuler tf tg := by
  intro h
  have := congrArg Fin.val h
  simp [firstMap, firstRuler] at this
  omega

theorem secondMap_ne_secondRuler (o : Fin tf) (j : Fin tg) : secondMap tf tg o j ≠ secondRuler tf tg := by
  intro h
  have h1 := congrArg Fin.val h
  have := o.isLt
  have := j.isLt
  by_cases hj : j.val = 0
  · rw [secondMap_zero tf tg o j hj, firstMap_val] at h1
    simp [secondRuler] at h1
    omega
  · rw [secondMap_val tf tg o j hj] at h1
    simp [secondRuler] at h1
    omega

/-- The rulers: the first program's budget on its ruler, the second's on its own, every other stream empty. -/
def pipeLens (bf bg : ℕ) (i : Fin (pipeStreams tf tg + 1)) : ℕ :=
  if i.val = tf + tg then bf else if i.val = tf + tg + 1 then bg else 0

/-- The output stream: the output tape of the second program. -/
def pipeOut (o : Fin tf) (og : Fin tg) : Fin (pipeStreams tf tg + 1) := secondMap tf tg o og

/-- The two-bank program: the first program, then the second. -/
noncomputable def pipeProgram {sf sg : ℕ} (Mf : Machine tf sf) (Mg : Machine tg sg) (o : Fin tf) :
    WMX (pipeStreams tf tg) 0 :=
  .seq (WMX.machZ Mf (firstMap tf tg) (firstRuler tf tg))
    (WMX.machZ Mg (secondMap tf tg o) (secondRuler tf tg))

end Layout

variable {Request : Type} {input middle output : Request → List Bool} {bf bg : Request → ℕ}

/-- The output stream of the composed program is not stream `0`. -/
theorem pipeOut_ne_zero (f : WordFunction Request input (fun r => frame (middle r)) bf)
    (g : WordFunction Request middle output bg) :
    (pipeOut f.program.tapeCount g.program.tapeCount f.program.outputTape g.program.outputTape).val ≠ 0 := by
  unfold pipeOut
  rw [secondMap_val _ _ _ _ g.program.outputFresh]
  have := f.program.twoTapes
  omega

/-- **The run of the composed program**: from the ideal start with both rulers, the first program leaves
`frame (m r)` on its output stream, the second program reads it there and leaves `output r` on the output
stream, in `2 b_f + 2 b_g + 5` steps. -/
theorem pipe_run (f : WordFunction Request input (fun r => frame (middle r)) bf)
    (g : WordFunction Request middle output bg) (r : Request) :
    pipeLens f.program.tapeCount g.program.tapeCount (bf r) (bg r)
        (pipeOut f.program.tapeCount g.program.tapeCount f.program.outputTape g.program.outputTape) = 0 ∧
      ∃ τ : WState (pipeStreams f.program.tapeCount g.program.tapeCount) 0,
        WXExec 0 (pipeProgram f.program.tapeCount g.program.tapeCount f.program.machine g.program.machine
          f.program.outputTape)
          (idealStart _ 0 (input r) (pipeLens f.program.tapeCount g.program.tapeCount (bf r) (bg r))) τ
          (2 * bf r + 2 * bg r + 5) ∧
        τ.st (pipeOut f.program.tapeCount g.program.tapeCount f.program.outputTape g.program.outputTape) =
          output r := by
  set tf := f.program.tapeCount with htf
  set tg := g.program.tapeCount with htg
  have hf2 := f.program.twoTapes
  have hg2 := g.program.twoTapes
  have hof := f.program.outputTape.isLt
  have hog := g.program.outputTape.isLt
  have hog0 := g.program.outputFresh
  set lens := pipeLens tf tg (bf r) (bg r) with hlens
  set σ0 : WState (pipeStreams tf tg) 0 := idealStart _ 0 (input r) lens with hσ0
  -- the ideal start, stream by stream
  have hst0 : ∀ i : Fin (pipeStreams tf tg + 1), σ0.st i =
      if i.val = 0 then frame (input r) else List.replicate (lens i) false := fun i => rfl
  have hsh0 : ∀ i : Fin (pipeStreams tf tg + 1), σ0.sh i = 0 := fun i => rfl
  have hlens_other : ∀ i : Fin (pipeStreams tf tg + 1), i.val < tf + tg → lens i = 0 := by
    intro i hi
    simp only [hlens, pipeLens]
    rw [if_neg (by omega), if_neg (by omega)]
  have hout_val : (pipeOut tf tg f.program.outputTape g.program.outputTape).val = tf + g.program.outputTape.val := by
    unfold pipeOut
    rw [secondMap_val _ _ _ _ hog0]
  refine ⟨hlens_other _ (by rw [hout_val]; omega), ?_⟩
  -- the first program
  obtain ⟨rf, hrf, hof'⟩ := f.realizes r
  have hinF : (fun j => σ0.st (firstMap tf tg j)) = f.program.inputTapes (input r) := by
    funext j
    rw [hst0, firstMap_val]
    unfold Program.inputTapes
    by_cases hj : j.val = 0
    · rw [if_pos hj, if_pos hj]
    · rw [if_neg hj, if_neg hj, hlens_other _ (by rw [firstMap_val]; omega)]
      rfl
  have hrunF : LocalBitMultitape.run f.program.machine (bf r) (fun j => σ0.st (firstMap tf tg j)) = some rf := by
    rw [hinF]
    exact hrf
  have hRf_st : σ0.st (firstRuler tf tg) = List.replicate (bf r) false := by
    rw [hst0]
    have h1 : (firstRuler tf tg).val = tf + tg := rfl
    rw [if_neg (by omega)]
    congr 1
    simp [hlens, pipeLens, h1]
  obtain ⟨σ1, e1, d1⟩ := WXExec.machZ_run (nr := 0) 0 (firstMap_injective tf tg) (firstMap_ne_firstRuler tf tg) σ0
    hrunF (fun j => hsh0 _) hRf_st (hsh0 _) le_rfl
  -- streams outside the first bank are untouched
  have hfar1 : ∀ i : Fin (pipeStreams tf tg + 1), tf ≤ i.val → σ1.st i = σ0.st i ∧ σ1.sh i = σ0.sh i := by
    intro i hi
    apply d1.other
    intro j hj
    have := congrArg Fin.val hj
    rw [firstMap_val] at this
    have := j.isLt
    omega
  -- the second program
  obtain ⟨rg, hrg, hog'⟩ := g.realizes r
  have hinG : (fun j => σ1.st (secondMap tf tg f.program.outputTape j)) = g.program.inputTapes (middle r) := by
    funext j
    unfold Program.inputTapes
    by_cases hj : j.val = 0
    · rw [if_pos hj, secondMap_zero _ _ _ _ hj, d1.st, hof']
    · rw [if_neg hj]
      have hv := secondMap_val tf tg f.program.outputTape j hj
      have hjl := j.isLt
      rw [(hfar1 _ (by rw [hv]; omega)).1, hst0, hv, if_neg (by omega),
        hlens_other _ (by rw [hv]; omega)]
      rfl
  have hrunG : LocalBitMultitape.run g.program.machine (bg r)
      (fun j => σ1.st (secondMap tf tg f.program.outputTape j)) = some rg := by
    rw [hinG]
    exact hrg
  have hshG : ∀ j, σ1.sh (secondMap tf tg f.program.outputTape j) = 0 := by
    intro j
    by_cases hj : j.val = 0
    · rw [secondMap_zero _ _ _ _ hj, d1.sh]
    · have hv := secondMap_val tf tg f.program.outputTape j hj
      rw [(hfar1 _ (by rw [hv]; omega)).2, hsh0]
  have hRg : σ1.st (secondRuler tf tg) = List.replicate (bg r) false ∧ σ1.sh (secondRuler tf tg) = 0 := by
    have h1 : (secondRuler tf tg).val = tf + tg + 1 := rfl
    obtain ⟨hs, hh⟩ := hfar1 (secondRuler tf tg) (by rw [h1]; omega)
    refine ⟨?_, by rw [hh, hsh0]⟩
    rw [hs, hst0, if_neg (by omega)]
    congr 1
    simp [hlens, pipeLens, h1]
  obtain ⟨σ2, e2, d2⟩ := WXExec.machZ_run (nr := 0) 0 (secondMap_injective tf tg f.program.outputTape)
    (secondMap_ne_secondRuler tf tg f.program.outputTape) σ1 hrunG hshG hRg.1 hRg.2 le_rfl
  refine ⟨σ2, WXExec.seq' 0 e1 e2 (by omega), ?_⟩
  show σ2.st (secondMap tf tg f.program.outputTape g.program.outputTape) = output r
  rw [d2.st, hog']

/-- **Sequential composition of word functions.** If `f` maps `input r` to the framed word `frame (middle r)` and
`g` maps `middle r` to `output r`, then one program maps `input r` to `output r` with budget `4 b_f + 4 b_g + 12`. -/
noncomputable def WordFunction.pipe (f : WordFunction Request input (fun r => frame (middle r)) bf)
    (g : WordFunction Request middle output bg) :
    WordFunction Request input output (fun r => 4 * bf r + 4 * bg r + 12) :=
  wordFunction_of_ideal
    (pipeProgram f.program.tapeCount g.program.tapeCount f.program.machine g.program.machine f.program.outputTape)
    (pipeOut f.program.tapeCount g.program.tapeCount f.program.outputTape g.program.outputTape)
    (pipeOut_ne_zero f g) (fun _ => 0)
    (fun r => pipeLens f.program.tapeCount g.program.tapeCount (bf r) (bg r))
    (fun r => 2 * bf r + 2 * bg r + 5) (fun r => by omega) (pipe_run f g)

end NearQuarticWires.Program
