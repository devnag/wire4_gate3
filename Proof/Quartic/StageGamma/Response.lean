import Proof.Quartic.StageGamma.Prepared
import Proof.Wire_3_5.PrimAsmSymDecCounts

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageGamma

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.SymDec
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Interfaces
open NearCubicGates.Close.Expand.PolyTab

variable {ns nr : ℕ}

/-- `cor:conditional`, paper/paper.tex: place the
consistency bit after the unary exponent's delimiter. -/
def appendGaussFlag (FLAG EXP : Fin (ns + 1)) : WM ns nr :=
  .seq (skipItemW EXP) (.ifs FLAG (.wr EXP true) (.wr EXP false))

/-- `cor:conditional`, paper/paper.tex: the response
contains both Gaussian outputs after a linear physical scan. -/
theorem appendGaussFlag_run (cap : ℕ) (FLAG EXP : Fin (ns + 1)) (hne : FLAG ≠ EXP)
    (σ : WState ns nr) (flag : Bool) (e : ℕ)
    (hf : σ.st FLAG = [flag]) (hhf : σ.sh FLAG = 0)
    (he : σ.st EXP = List.replicate e true ++ [false]) (hhe : σ.sh EXP = 0) :
    WExec cap (appendGaussFlag FLAG EXP) σ
      ((σ.seth EXP (e + 1)).sets EXP (List.replicate e true ++ [false, flag]))
      (3 * e + 6) := by
  have hs := skipItem_spec cap EXP [] [] e σ (by simpa using he) (by simpa using hhe)
  simp only [List.length_nil, Nat.zero_add] at hs
  let τ := σ.seth EXP (e + 1)
  have hfτ : wbit τ FLAG = flag := by
    unfold wbit readTapeBit
    simp [τ, Function.update_of_ne hne, hf, hhf]
  have hw : writeTapeBit (τ.st EXP) (τ.sh EXP) flag =
      List.replicate e true ++ [false, flag] := by
    have hl : (σ.st EXP).length = e + 1 := by simp [he]
    simp only [τ, WState.seth_st, WState.seth_sh, Function.update_self]
    rw [← hl, writeTapeBit_end', he]
    simp
  have hwrite : WExec cap (.ifs FLAG (.wr EXP true) (.wr EXP false)) τ
      (τ.sets EXP (List.replicate e true ++ [false, flag])) 2 := by
    cases flag
    · simpa only [hw] using
        WExec.ifsF (Q := WM.wr EXP false) (P := WM.wr EXP true)
          hfτ (WExec.wr (cap := cap) EXP false τ)
    · simpa only [hw] using
        WExec.ifsT (Q := WM.wr EXP false) (P := WM.wr EXP true)
          hfτ (WExec.wr (cap := cap) EXP true τ)
  exact WExec.mono (WExec.seq hs hwrite) (by omega)

/-- `cor:conditional`, paper/paper.tex: one compact
Gaussian reply consists of nullity in unary followed by its flag. -/
noncomputable def preparedResponse (r : PreparedRequest) : List Bool :=
  List.replicate (kernelExponent r.1 r.2) true ++ [false, kernelFlag r.1 r.2]

/-- `cor:conditional`, paper/paper.tex: the complete
subroutine uses one fixed decoder, one Gaussian call and one output scan. -/
noncomputable def preparedResponseProgram : WMX 32 1 :=
  .seq preparedProgram (.wm (appendGaussFlag (kernelSlot 29) (kernelSlot 30)))

/-- `prop:time`, paper/paper.tex: every output scan
is paid in addition to decoding and Gaussian elimination. -/
noncomputable def preparedResponseCost (r : PreparedRequest) : ℕ :=
  preparedCost r + 1 + (3 * kernelExponent r.1 r.2 + 6)

/-- `cor:conditional`, paper/paper.tex: an actual cold
word function returns both exact conjunction outputs in one response. -/
noncomputable def preparedGaussWordFunction :
    WordFunction PreparedRequest preparedInput preparedResponse
      (fun r => 2 * preparedResponseCost r + 2) :=
  wordFunction_of_ideal preparedResponseProgram (kernelSlot 30) (by decide)
    preparedCapacity (fun _ _ => 0) preparedResponseCost (fun _ => le_rfl) (by
      intro r
      obtain ⟨τ, hr, hf, he, hhf, hhe⟩ := prepared_run r
      have hscan := appendGaussFlag_run (preparedCapacity r) (kernelSlot 29) (kernelSlot 30)
        (by decide) τ (kernelFlag r.1 r.2) (kernelExponent r.1 r.2) hf hhf he hhe
      let ρ := (τ.seth (kernelSlot 30) (kernelExponent r.1 r.2 + 1)).sets (kernelSlot 30)
        (preparedResponse r)
      refine ⟨rfl, ρ, ?_, ?_⟩
      · simpa only [idealStart, startState, List.replicate_zero, preparedResponseProgram,
          preparedResponseCost, ρ, preparedResponse] using WXExec.seq hr (WXExec.wm hscan)
      · simp only [ρ, WState.sets_st, Function.update_self])

/-- `prop:time`, paper/paper.tex: the compact reply's
scan length is bounded by the original seed length. -/
theorem preparedResponseCost_le (r : PreparedRequest) :
    preparedResponseCost r ≤ 46 * (preparedInput r).length + 15 +
      3 * Cycle.seedLength r.1.parameters +
      3000 * (Cycle.seedLength r.1.parameters + 9) ^ 6 := by
  have hp := preparedCost_le r
  have he : kernelExponent r.1 r.2 ≤ Cycle.seedLength r.1.parameters := by
    dsimp [kernelExponent, Cycle.seedLength]
    omega
  dsimp [preparedResponseCost]
  omega

end NearQuarticWires.StageGamma
