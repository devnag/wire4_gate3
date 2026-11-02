import Proof.Quartic.StageNativeHeader.Width

/-!
# The cut census

Paper: `lem:print` and `prop:time`, paper/paper.tex.

`countP` copies the marked cut bytes of the input once, unmarked, to `sX`, moves both heads back, and counts the cuts
on `sX` at their frame boundaries with the sealed `CutScan.countRows` (stride `2·width + 2`), the count in `rG`
(`count_exec`). No count or length is supplied; an empty cut stream gives `0`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageNativeHeader

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.Streaming (marks marks_append)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO appendO_st appendO_sh appendO_val appendO_cell)
open NearCubicGates.Close.Recovery.HTParts (pairLoop pairLoop_spec emits_none emits_raw adv)
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearQuarticWires.Control NearQuarticWires.StagePrint NearQuarticWires.StagePrint.Downstream

variable (cap : ℕ)

/-- The counters of the census. -/
def rSC0 : Fin hnr := 30
def rOX : Fin hnr := 31
def cR0 : Fin hnr := 32
def cR1 : Fin hnr := 33
def cR3 : Fin hnr := 34
def cR4 : Fin hnr := 35

/-- The registers of the cut counter (stride in `rT2`, count in `rG`). -/
def Rc : Fin 6 ↪ Fin hnr := ⟨![cR0, cR1, rT2, cR3, cR4, rG], by decide⟩

/-- Copy the marked cut bytes unmarked to `sX`, move back, count. -/
noncomputable def countP : WM hns hnr :=
  .seq (pairLoop sIN rSC0 (fun _ => WM.skip) (fun b => emitC sX rOX b))
    (.seq (WM.rewind sX rOX) (.seq (WM.rewind sIN rSC0) (.seq (CutScan.countRows sX Rc) (WM.clear cR1))))

/-- The cost of `countP`. -/
def countCost (r : NativeHeaderRequest) : ℕ :=
  r.stream.length * 24 + 1 + 5 * r.stream.length + 1 + 10 * r.stream.length + 1 +
    (25 * r.stream.length + r.table.matrix.cuts.length * (22 * (2 * PrimT.C4Geo.width r.parameters + 2) + 11) + 1) +
    3 * r.stream.length + 1 + 4

theorem hX_ne_IN : sX ≠ sIN := sne (by simp [sX, sIN, strm])

/-- **The cut census.** -/
theorem count_exec (r : NativeHeaderRequest) (σ : WState hns hnr) (pre : List Bool)
    (hin : σ.st sIN = pre ++ marks r.stream ++ [false]) (hinh : σ.sh sIN = pre.length)
    (hX : σ.st sX = []) (hXh : σ.sh sX = 0) (hCD : σ.st sCD = []) (hCDh : σ.sh sCD = 0)
    (vT2 : σ.val rT2 = 2 * PrimT.C4Geo.width r.parameters + 2)
    (hz : ∀ y ∈ [rSC0, rOX, cR0, cR1, cR3, cR4, rG], σ.val y = 0)
    (hcap : 4 * r.stream.length + 2 * PrimT.C4Geo.width r.parameters + r.table.matrix.cuts.length + 4 ≤ cap) :
    ∃ τ, WExec cap countP σ τ (countCost r) ∧ SOnly σ τ [sX, sCD] [rG] ∧
      τ.val rG = r.table.matrix.cuts.length := by
  set S := r.stream with hS
  -- the unmarked copy
  have e1 := pairLoop_spec cap (src := sIN) (dst := sX) (OP := rOX) (SC := rSC0) (Ne.symm hX_ne_IN) (by decide)
    (emits_none cap) (emits_raw cap) [false] rfl S pre σ (by rw [hin]) hinh (by rw [hX, hXh]; rfl)
    (by rw [hz rOX (by simp)]; simp; omega) (by rw [hz rSC0 (by simp)]; omega)
  have hu : (S.flatMap fun b => ([] : List Bool) ++ [b]) = S := by simp
  rw [hu] at e1
  set σ1 := adv sIN sX rOX rSC0 σ S (2 * S.length) with hσ1
  have v1X : σ1.st sX = S ∧ σ1.sh sX = S.length := by
    simp [hσ1, adv, hX, hXh, Function.update_of_ne hX_ne_IN]
  have v1I : σ1.st sIN = σ.st sIN ∧ σ1.sh sIN = pre.length + 2 * S.length := by
    simp [hσ1, adv, Function.update_of_ne (Ne.symm hX_ne_IN), hinh]
  have v1v : ∀ y, y ≠ rOX → y ≠ rSC0 → σ1.val y = σ.val y := fun y h1 h2 => by
    simp [hσ1, adv, Function.update_of_ne h1, Function.update_of_ne h2]
  have v1OX : σ1.val rOX = S.length := by
    simp [hσ1, adv, Function.update_of_ne (show (rOX : Fin hnr) ≠ rSC0 by decide), hz rOX (by simp)]
  have v1SC : σ1.val rSC0 = 2 * S.length := by simp [hσ1, adv, hz rSC0 (by simp)]
  -- back to the starts
  have e2 := wrewind_spec cap sX rOX S.length σ1 v1OX (by omega)
  set σ2 := (σ1.setv rOX 0).seth sX (σ1.sh sX - S.length) with hσ2
  have e3 := wrewind_spec cap sIN rSC0 (2 * S.length) σ2
    (by simp [hσ2, Function.update_of_ne (show (rSC0 : Fin hnr) ≠ rOX by decide), v1SC]) (by
      simp [hσ2, Function.update_of_ne (show (rSC0 : Fin hnr) ≠ rOX by decide), v1SC]; omega)
  set σ3 := (σ2.setv rSC0 0).seth sIN (σ2.sh sIN - 2 * S.length) with hσ3
  have v3X : σ3.st sX = [] ++ S ++ [] ∧ σ3.sh sX = ([] : List Bool).length := by
    simp [hσ3, hσ2, Function.update_of_ne hX_ne_IN, v1X.1, v1X.2]
  have v3I : σ3.st sIN = σ.st sIN ∧ σ3.sh sIN = σ.sh sIN := by
    simp [hσ3, hσ2, Function.update_of_ne (Ne.symm hX_ne_IN), v1I.1, v1I.2, hinh]
  have v3v : ∀ y, y ≠ rOX → y ≠ rSC0 → σ3.val y = σ.val y := fun y h1 h2 => by
    simp [hσ3, hσ2, Function.update_of_ne h1, Function.update_of_ne h2, v1v y h1 h2]
  have v3z : σ3.val rOX = 0 ∧ σ3.val rSC0 = 0 := by
    simp [hσ3, hσ2, Function.update_of_ne (show (rOX : Fin hnr) ≠ rSC0 by decide)]
  -- the census
  have hCDX : sX ≠ sCD := sne (by simp [sX, sCD, strm])
  have e4 := CutScan.nativeCutCount_spec cap sX sCD Rc hCDX (PrimT.C4Geo.width r.parameters) r.table.matrix.p
    r.table.matrix.cuts (fun c hc => by rw [← r.width_eq]; exact r.table.matrix.lengths c hc) [] [] rfl σ3
    (by rw [v3X.1]; rfl) v3X.2
    (by simp [hσ3, hσ2, hσ1, adv, Function.update_of_ne (show sCD ≠ sIN from sne (by simp [sCD, sIN, strm])),
      Function.update_of_ne (Ne.symm hCDX), hCD, hCDh])
    (by rw [show Rc 2 = rT2 from rfl, v3v _ (by decide) (by decide), vT2])
    (by rw [show Rc 3 = cR3 from rfl, v3v _ (by decide) (by decide), hz cR3 (by simp)])
    (by rw [show Rc 4 = cR4 from rfl, v3v _ (by decide) (by decide), hz cR4 (by simp)])
    (by rw [show Rc 0 = cR0 from rfl, v3v _ (by decide) (by decide), hz cR0 (by simp)]; omega)
    (by rw [show Rc 1 = cR1 from rfl, v3v _ (by decide) (by decide), hz cR1 (by simp)]; show 0 + S.length ≤ cap
        omega)
    (by omega)
    (by rw [show Rc 5 = rG from rfl, v3v _ (by decide) (by decide), hz rG (by simp)]; omega)
  set σ4 := (adv sX sCD (Rc 0) (Rc 1) σ3 [] (r.table.matrix.cuts.flatMap (MatrixScoreBatch.cutWord r.table.matrix.p)).length).setv
    (Rc 5) (σ3.val (Rc 5) + r.table.matrix.cuts.length) with hσ4
  have v4C : σ4.val cR1 = S.length := by
    simp [hσ4, adv, show Rc 1 = cR1 from rfl, show Rc 5 = rG from rfl, show Rc 0 = cR0 from rfl,
      Function.update_of_ne (show (cR1 : Fin hnr) ≠ rG by decide), v3v cR1 (by decide) (by decide),
      hz cR1 (by simp), hS, NativeHeaderRequest.stream]
  have e5 := wclear_spec cap cR1 S.length σ4 v4C (by omega)
  have v4st : ∀ i, i ≠ sCD → σ4.st i = σ3.st i := fun i h => by simp [hσ4, adv, Function.update_of_ne h]
  have v4sh : ∀ i, i ≠ sCD → i ≠ sX → σ4.sh i = σ3.sh i := fun i h1 h2 => by
    simp [hσ4, adv, Function.update_of_ne h1, Function.update_of_ne h2]
  have v3st : ∀ i, i ≠ sX → σ3.st i = σ.st i := fun i h => by
    simp [hσ3, hσ2, hσ1, adv, Function.update_of_ne h]
  have v3sh : ∀ i, i ≠ sX → i ≠ sIN → σ3.sh i = σ.sh i := fun i h1 h2 => by
    simp [hσ3, hσ2, hσ1, adv, Function.update_of_ne h1, Function.update_of_ne h2]
  refine ⟨σ4.setv cR1 0, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))) ?_, ⟨fun i hi => ?_,
    fun i hi => ?_, fun y hy => ?_⟩, ?_⟩
  · unfold countCost
    simp only [hS, NativeHeaderRequest.stream] at *
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    rw [show (σ4.setv cR1 0).st i = σ4.st i from rfl, v4st i hi.2, v3st i hi.1]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    rw [show (σ4.setv cR1 0).sh i = σ4.sh i from rfl, v4sh i hi.2 hi.1]
    by_cases hI : i = sIN
    · subst hI; exact v3I.2
    · exact v3sh i hi.1 hI
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    by_cases h1 : y = cR1
    · subst h1; simp [hz cR1 (by simp)]
    · by_cases h0 : y = cR0
      · subst h0
        simp [hσ4, adv, show Rc 1 = cR1 from rfl, show Rc 5 = rG from rfl, show Rc 0 = cR0 from rfl,
          Function.update_of_ne (show (cR0 : Fin hnr) ≠ rG by decide),
          Function.update_of_ne (show (cR0 : Fin hnr) ≠ cR1 by decide), v3v cR0 (by decide) (by decide)]
      · by_cases h2 : y = rOX
        · subst h2
          simp [hσ4, adv, show Rc 1 = cR1 from rfl, show Rc 5 = rG from rfl, show Rc 0 = cR0 from rfl,
            Function.update_of_ne (show (rOX : Fin hnr) ≠ rG by decide), Function.update_of_ne h1,
            Function.update_of_ne h0, v3z.1, hz rOX (by simp)]
        · by_cases h3 : y = rSC0
          · subst h3
            simp [hσ4, adv, show Rc 1 = cR1 from rfl, show Rc 5 = rG from rfl, show Rc 0 = cR0 from rfl,
              Function.update_of_ne (show (rSC0 : Fin hnr) ≠ rG by decide), Function.update_of_ne h1,
              Function.update_of_ne h0, v3z.2, hz rSC0 (by simp)]
          · simp [hσ4, adv, show Rc 1 = cR1 from rfl, show Rc 5 = rG from rfl, show Rc 0 = cR0 from rfl,
              Function.update_of_ne hy, Function.update_of_ne h1, Function.update_of_ne h0, v3v y h2 h3]
  · simp [hσ4, show Rc 5 = rG from rfl, Function.update_of_ne (show (rG : Fin hnr) ≠ cR1 by decide),
      v3v rG (by decide) (by decide), hz rG (by simp)]

end NearQuarticWires.StageNativeHeader
