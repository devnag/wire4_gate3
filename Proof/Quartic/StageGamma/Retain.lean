import Proof.Gates.Codec.Unframe
import Proof.Gates.CounterMachine.TabCallDock
import Proof.Gates.Expand.PolyTabPack

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageGamma

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Codec
open NearCubicGates.Close.CounterMachine
open NearCubicGates.Close.Expand.PolyTab

variable {Request : Type} {input cache : Request → List Bool} {budget : Request → ℕ}

/-- `cor:conditional`, paper/paper.tex: the cached
setup runs on a separate physical bank, leaving stream zero untouched. -/
def retainedMap (t : ℕ) (j : Fin t) : Fin (t + 3) := ⟨j.val + 1, by omega⟩

/-- `cor:conditional`, paper/paper.tex: the retained
setup bank has no overlapping input or work streams. -/
theorem retainedMap_injective (t : ℕ) : Function.Injective (retainedMap t) := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  dsimp [retainedMap] at this
  omega

/-- `cor:conditional`, paper/paper.tex: the single
cached setup call has its own once-only physical reset ruler. -/
def retainedRuler (t : ℕ) : Fin (t + 3) := ⟨t + 1, by omega⟩

/-- `cor:conditional`, paper/paper.tex: a fresh
stream receives the original source followed by the computed cached data. -/
def retainedOut (t : ℕ) : Fin (t + 3) := ⟨t + 2, by omega⟩

/-- `cor:conditional`, paper/paper.tex: the setup
ruler is outside every stream used by the cached computation. -/
theorem retainedMap_ne_ruler (t : ℕ) (j : Fin t) :
    retainedMap t j ≠ retainedRuler t := by
  intro h
  have := congrArg Fin.val h
  dsimp [retainedMap, retainedRuler] at this
  omega

/-- `cor:conditional`, paper/paper.tex: no cached
setup stream aliases the untouched original input or final handoff output. -/
theorem retainedMap_off (t : ℕ) (j : Fin t) :
    retainedMap t j ≠ (0 : Fin (t + 3)) ∧ retainedMap t j ≠ retainedOut t := by
  constructor <;> intro h <;> have hh := congrArg Fin.val h <;>
    simp only [retainedMap, retainedOut, Fin.val_zero] at hh <;> omega

/-- `cor:conditional`, paper/paper.tex: fixed finite
control copies the ORIGINAL input, computes the cache once, then physically
writes one framed handoff word containing both exact payloads. -/
noncomputable def retainedProgram
    (f : WordFunction Request input (fun r => frame (cache r)) budget) :
    WMX (f.program.tapeCount + 2) 3 :=
  let t := f.program.tapeCount
  .seq (.wm (copyRW 0 (retainedMap t (tape0 f.program)) 0 1 2))
    (.seq (.machZ f.program.machine (retainedMap t) (retainedRuler t))
      (.seq (.wm (.whs 0 (copyPairW 0 (retainedOut t) 0)))
        (.seq (.wm (.whs (retainedMap t f.program.outputTape)
          (copyPairW (retainedMap t f.program.outputTape) (retainedOut t) 0)))
          (.wm (emitC (retainedOut t) 0 false)))))

/-- `prop:time`, paper/paper.tex: physical retained
input and cache copying are charged linearly, in addition to one setup call. -/
def retainedCost (r : Request) : ℕ :=
  2 * budget r + 150 * ((input r).length + (cache r).length + 1)

/-- `cor:conditional`, paper/paper.tex: only the
once-only setup ruler is nonempty blank workspace at the ideal start. -/
def retainedLens (t : ℕ) (b : ℕ) (i : Fin (t + 3)) : ℕ :=
  if i.val = t + 1 then b else 0

/-- `prop:time`, paper/paper.tex: the finite
copying registers have an explicit linear capacity in the two actual words. -/
def retainedCapacity (r : Request) : ℕ :=
  4 * ((input r).length + (cache r).length + 1) + 4

/-- `cor:conditional` and `prop:time`, paper/paper.tex: the cached computation is invoked once on a real input copy;
the ORIGINAL source is preserved outside its bank and both payloads are
physically printed for the next stage. -/
theorem retained_run
    (f : WordFunction Request input (fun r => frame (cache r)) budget) (r : Request) :
    ∃ τ, WXExec (retainedCapacity (input := input) (cache := cache) r)
      (retainedProgram f)
      (idealStart (f.program.tapeCount + 2) 3 (input r)
        (retainedLens f.program.tapeCount (budget r))) τ
      (retainedCost (input := input) (cache := cache) (budget := budget) r) ∧
      τ.st (retainedOut f.program.tapeCount) = frame (input r ++ cache r) := by
  let t := f.program.tapeCount
  let cap := retainedCapacity (input := input) (cache := cache) r
  let σ := idealStart (t + 2) 3 (input r) (retainedLens t (budget r))
  have ht : 2 ≤ t := f.program.twoTapes
  have hm0 : retainedMap t (tape0 f.program) = (1 : Fin (t + 3)) := by
    apply Fin.ext
    change (0 + 1 : ℕ) = 1 % (t + 3)
    rw [Nat.mod_eq_of_lt (by omega)]
  have hsrc : σ.st 0 = frame (input r) := by simp [σ, idealStart]
  have hdst : σ.st (retainedMap t (tape0 f.program)) = [] := by
    simp [σ, idealStart, retainedLens, retainedMap, tape0]
    omega
  have hc := copyRW_spec cap (0 : Fin (t + 3)) (retainedMap t (tape0 f.program))
    ((retainedMap_off t (tape0 f.program)).1.symm) (0 : Fin 3) 1 2
    (by decide) (by decide) (by decide)
    (input r) [] σ (by simpa using hsrc) rfl hdst rfl rfl rfl rfl
    (by dsimp [cap, retainedCapacity]; omega)
  let σ1 := σ.sets (retainedMap t (tape0 f.program)) (frame (input r))
  have h1in : σ1.st (retainedMap t (tape0 f.program)) = frame (input r) := by simp [σ1]
  have h1blank : ∀ j, j ≠ tape0 f.program → σ1.st (retainedMap t j) = [] := by
    intro j hj
    have hne : retainedMap t j ≠ retainedMap t (tape0 f.program) :=
      fun h => hj (retainedMap_injective t h)
    have hjr := retainedMap_ne_ruler t j
    have hj0 := (retainedMap_off t j).1
    simp only [σ1, WState.sets_st, Function.update_of_ne hne]
    simp [σ, idealStart, retainedLens, hj0, retainedMap]
    omega
  have h1ruler : σ1.st (retainedRuler t) = List.replicate (budget r) false := by
    have hne := (retainedMap_ne_ruler t (tape0 f.program)).symm
    simp only [σ1, WState.sets_st, Function.update_of_ne hne]
    simp [σ, idealStart, retainedRuler, retainedLens]
  obtain ⟨σ2, hcall, houtput, hheads, hoff, hregs⟩ :=
    wfDock_exact f r cap (retainedMap t) (retainedMap_injective t) (retainedRuler t)
      (retainedMap_ne_ruler t) σ1 h1in h1blank (fun _ => rfl)
      (budget r) h1ruler rfl le_rfl
  have h20 := hoff 0 (fun j => (retainedMap_off t j).1)
  have h2out := hoff (retainedOut t) (fun j => (retainedMap_off t j).2)
  have hσ2src : σ2.st 0 = frame (input r) := by
    rw [h20.1]
    simp [σ1, (retainedMap_off t (tape0 f.program)).1.symm, hsrc]
  have hσ2out : σ2.st (retainedOut t) = [] := by
    rw [h2out.1]
    simp only [σ1, WState.sets_st,
      Function.update_of_ne (retainedMap_off t (tape0 f.program)).2.symm]
    simp [σ, idealStart, retainedOut, retainedLens]
  have hσ2h0 : σ2.sh 0 = 0 := h20.2
  have hσ2hout : σ2.sh (retainedOut t) = 0 := h2out.2
  have hv0 : σ2.val 0 = 0 := by rw [hregs]; rfl
  have hfirst := copyFrame_loop cap (0 : Fin (t + 3)) (retainedOut t)
    (by simp [retainedOut]) (0 : Fin 3) [] (input r) [] σ2
    (by simpa using hσ2src) hσ2h0 (by rw [hσ2hout, hσ2out]; rfl)
    (by rw [hv0]; dsimp [cap, retainedCapacity]; omega)
  simp only [List.length_nil, Nat.zero_add] at hfirst
  let σ3 := (appendO σ2 (retainedOut t) 0 (Streaming.marks (input r))).seth 0 (2 * (input r).length)
  have h3cache : σ3.st (retainedMap t f.program.outputTape) = frame (cache r) := by
    have hne := (retainedMap_off t f.program.outputTape).2
    simp [σ3, appendO, Function.update_of_ne hne, houtput]
  have h3cachehead : σ3.sh (retainedMap t f.program.outputTape) = 0 := by
    have hne := (retainedMap_off t f.program.outputTape).2
    have hn0 := (retainedMap_off t f.program.outputTape).1
    simp [σ3, appendO, Function.update_of_ne hne, Function.update_of_ne hn0, hheads]
  have h3out : σ3.st (retainedOut t) = Streaming.marks (input r) := by
    simp [σ3, appendO, hσ2out]
  have h3hout : σ3.sh (retainedOut t) = (Streaming.marks (input r)).length := by
    have hne : retainedOut t ≠ (0 : Fin (t + 3)) := by simp [retainedOut]
    simp only [σ3, appendO, WState.seth_sh, WState.setv_sh,
      Function.update_of_ne hne, Function.update_self, hσ2hout, Nat.zero_add]
  have h3v : σ3.val 0 = 2 * (input r).length := by
    simp [σ3, appendO, hv0, Streaming.marks_length]
  have hsecond := copyFrame_loop cap (retainedMap t f.program.outputTape) (retainedOut t)
    ((retainedMap_off t f.program.outputTape).2) (0 : Fin 3) [] (cache r) [] σ3
    (by simpa using h3cache) h3cachehead (by rw [h3hout, h3out])
    (by rw [h3v]; dsimp [cap, retainedCapacity]; omega)
  simp only [List.length_nil, Nat.zero_add] at hsecond
  let σ4 := (appendO σ3 (retainedOut t) 0 (Streaming.marks (cache r))).seth
    (retainedMap t f.program.outputTape) (2 * (cache r).length)
  have h4out : σ4.st (retainedOut t) = Streaming.marks (input r) ++ Streaming.marks (cache r) := by
    simp [σ4, appendO, h3out]
  have h4hout : σ4.sh (retainedOut t) = (σ4.st (retainedOut t)).length := by
    simp [σ4, appendO, Function.update_of_ne
      ((retainedMap_off t f.program.outputTape).2.symm), h3hout, h3out, List.length_append]
  have h4v : σ4.val 0 < cap := by
    simp [σ4, appendO, h3v, Streaming.marks_length]
    dsimp [cap, retainedCapacity]
    omega
  have hlast := emitC_spec cap (retainedOut t) (0 : Fin 3) false σ4 h4hout h4v
  refine ⟨appendO σ4 (retainedOut t) 0 [false], ?_, ?_⟩
  · have hall := WXExec.seq (WXExec.wm hc) (WXExec.seq hcall
      (WXExec.seq (WXExec.wm hfirst) (WXExec.seq (WXExec.wm hsecond) (WXExec.wm hlast))))
    apply hall.mono
    dsimp [retainedCost]
    omega
  · change (appendO σ4 (retainedOut t) 0 [false]).st (retainedOut t) = _
    simp only [appendO, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_self, h4out]
    rw [NearCubicGates.Close.Codec.frame_eq_marks, Streaming.marks_append]

/-- `cor:conditional`, paper/paper.tex: one genuine
cold function retains the ORIGINAL source and appends the computed cache,
with copying and one setup search included in its physical budget. -/
noncomputable def retainedWordFunction
    (f : WordFunction Request input (fun r => frame (cache r)) budget) :
    WordFunction Request input (fun r => frame (input r ++ cache r))
      (fun r => 2 * retainedCost (input := input) (cache := cache) (budget := budget) r + 2) :=
  wordFunction_of_ideal (retainedProgram f) (retainedOut f.program.tapeCount)
    (by simp [retainedOut]) (retainedCapacity (input := input) (cache := cache))
    (fun r => retainedLens f.program.tapeCount (budget r))
    (retainedCost (input := input) (cache := cache) (budget := budget)) (fun _ => le_rfl) (by
      intro r
      refine ⟨?_, retained_run f r⟩
      simp [retainedLens, retainedOut])

end NearQuarticWires.StageGamma
