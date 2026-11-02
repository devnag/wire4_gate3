import Proof.Quartic.StageHamming.EncoderPrefix
import Proof.Quartic.StagePullback.BitArithmetic

set_option autoImplicit false

namespace NearQuarticWires.StageHamming

open NearCubicGates.Close.Cells

def encoderCounter : Fin VV := 110
def encoderLimit : Fin VV := 111
def encoderBase : Fin VV := 112
def encoderAccumulator : Fin VV := 113
def encoderSelected : Fin VV := 119
def encoderCode : Fin VV := 126

/-- `imp:partition`, paper/paper.tex: an actual
selected scalar code bit controls whether its computed canonical
column is xored into the block accumulator. -/
def encoderAccumulate : St VV MM :=
  .ite (.eq encoderSelected v1)
    (StagePullback.xorInto encoderAccumulator columnOutput) skipS

/-- `imp:partition` and `prop:time`, paper/paper.tex: the canonical encoder update is physically realized by
one bit test and the actual scalar xor, with a complete constant clock. -/
theorem encoderAccumulate_spec {C : Ctx} (a : DS VV MM) (hc : Cst a)
    (old selected entry : Bool)
    (hacc : a.env encoderAccumulator = old.toNat)
    (hselected : a.env encoderSelected = selected.toNat)
    (hentry : a.env columnOutput = entry.toNat) :
    Hs C encoderAccumulate a 4 (fun b =>
      b.env encoderAccumulator = (xor old (selected && entry)).toNat ∧
      b.sh = a.sh ∧ Fr a b [encoderAccumulator, vJ]) := by
  cases selected with
  | false =>
    unfold encoderAccumulate
    refine Hs.mono (Hs.iteF (show encoderSelected ≠ v1 by decide)
      (by simp [Cnd.eval, hselected, hc.one]) (skip_spec a)) (by omega) ?_
    rintro b rfl
    refine ⟨?_, rfl, Fr.set _ _ (by simp)⟩
    rw [DS.set_env_ne _ _ (by decide), hacc]
    simp
  | true =>
    unfold encoderAccumulate
    refine Hs.iteT (show encoderSelected ≠ v1 by decide)
      (by simp [Cnd.eval, hselected, hc.one]) ?_
    exact (StagePullback.xorInto_run C encoderAccumulator columnOutput
      (by decide) (by decide) (by decide) a hc old entry hacc hentry).mono le_rfl
      (fun _ h => by simpa only [Bool.true_and] using h)

end NearQuarticWires.StageHamming
