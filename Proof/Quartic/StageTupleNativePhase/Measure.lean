import Proof.Quartic.StageTupleNativePhase.Call
import Proof.Wire_3_5.FinalPassHashTable
import Proof.Quartic.StageGamma.Unframe

set_option autoImplicit false

namespace NearQuarticWires.StageTupleNativePhase

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass.Hash4
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.WordPrograms

variable {ns : ℕ}

/-- `lem:print`, paper/paper.tex: two
retained counters record the measured framed reply and unframed payload
byte lengths, while the reply cursor is restored for physical decoding. -/
def measuredState (σ : WState ns 32) (src : Fin (ns+1)) (bits : List Bool) : WState ns 32 :=
  ((σ.sets src (frame bits)).setv 24 (frame bits).length).setv 25 bits.length

/-- `lem:print`, paper/paper.tex: both
length counters come from the actual copy counter; halving the framed
length after subtracting its delimiter obtains the real payload length. -/
def measureProgram (src : Fin (ns+1)) : WM ns 32 :=
  .seq (wcopyR 0 24 6) (.seq (wcopyR 0 25 6)
    (.seq (WM.rewind src 0) (.seq (.dec 25) (halveM 25 0 1))))

/-- `lem:print` and `prop:time`, paper/paper.tex: copying, rewinding and halving the actual
reply counter computes both byte lengths with a paid linear clock. -/
theorem measureProgram_spec (cap : ℕ) (src : Fin (ns+1)) (bits : List Bool)
    (σ : WState ns 32) (hst : σ.st src=[]) (hsh : σ.sh src=0)
    (h0 : σ.val 0=0) (h1 : σ.val 1=0) (h6 : σ.val 6=0)
    (h24 : σ.val 24=0) (h25 : σ.val 25=0) (hcap : (frame bits).length ≤ cap) :
    WExec cap (measureProgram src) (appendO σ src 0 (frame bits))
      (measuredState σ src bits) (100*(frame bits).length+100) := by
  let a := appendO σ src 0 (frame bits)
  have a0 : a.val 0=(frame bits).length := by simp [a, appendO, h0]
  have e1 := wcopyR_spec cap (0 : Fin 32) 24 6 (by decide) (by decide) (by decide) a
    (by simp [a, appendO, h24]) (by simp [a, appendO, h6]) (by rw [a0]; exact hcap)
  let b := a.setv 24 (a.val 0)
  have b0 : b.val 0=(frame bits).length := by simp [b, a0]
  have e2 := wcopyR_spec cap (0 : Fin 32) 25 6 (by decide) (by decide) (by decide) b
    (by simp [b, a, appendO, h25]) (by simp [b, a, appendO, h6]) (by rw [b0]; exact hcap)
  let c := b.setv 25 (b.val 0)
  have c0 : c.val 0=(frame bits).length := by simp [c, b0]
  have e3 := wrewind_spec cap src (0 : Fin 32) (frame bits).length c c0 (by rw [c0]; exact hcap)
  let d := (c.setv 0 0).seth src (c.sh src-(frame bits).length)
  have d25 : d.val 25=(frame bits).length := by simp [d, c, b0]
  have e4 := WExec.dec (cap:=cap) (25 : Fin 32) d (by rw [d25]; exact hcap)
  let e := d.setv 25 (d.val 25-1)
  have e25 : e.val 25=(frame bits).length-1 := by simp [e, d25]
  have e5 := halveM_spec cap (25 : Fin 32) 0 1 (by decide) (by decide) (by decide) e
    (by simp [e, d]) (by simp [e, d, c, b, a, appendO, h1])
    (by rw [e25]; omega) (by rw [frame_length] at hcap; omega)
  refine (e1.seq (e2.seq (e3.seq (e4.seq e5)))).cast cap ?_ ?_
  · apply WState.eq
    · funext i
      by_cases hi : i=src
      · subst i
        simp [e, d, c, b, a, appendO, measuredState, hsh]
      · simp [e, d, c, b, a, appendO, measuredState, hi]
    · simp [e, d, c, b, a, appendO, measuredState, hst]
    · funext i
      by_cases hi : i=25
      · subst i
        simp [measuredState, e25, frame_length]
      · by_cases h24i : i=24
        · subst i
          simp [measuredState, e, d, c, b, a0]
        · by_cases h1i : i=1
          · subst i
            simp [measuredState, e25, frame_length, h1]
          · by_cases h0i : i=0
            · subst i
              simp [measuredState, e, d, h0]
            · simp [measuredState, e, d, c, b, a, appendO, hi, h24i, h1i, h0i]
    · rfl
  · rw [a0, b0, e25]
    omega

end NearQuarticWires.StageTupleNativePhase
