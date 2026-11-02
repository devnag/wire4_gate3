import Proof.Quartic.StagePrintTuple.RecordsCopy

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKids

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.Recovery.HTParts

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: the five
nonempty actual source fields are copied with their outer output
markers, stopping at the first literal empty original-source field. -/
def appendMarkedRecordsReset (src dst : Fin (ns + 1)) (OP SC : Fin nr) : WM ns nr :=
  .seq (CounterAsm.frameLoop src SC (fun b => emitPair dst OP b)) (WM.rewind src SC)

/-- `lem:print` and `prop:time`, paper/paper.tex: every actual retained input bit and its new
marker are physically written, and the source cursor resets. -/
theorem appendMarkedRecordsReset_spec (cap : ℕ) (src dst : Fin (ns + 1))
    (OP SC : Fin nr) (hsd : src ≠ dst) (hOS : OP ≠ SC)
    (records : List (List Bool)) (rest : List Bool)
    (hne : ∀ record ∈ records, record ≠ []) (hend : rest.headD false = false)
    (σ : WState ns nr) (hs : σ.st src = records.flatMap frame ++ rest)
    (hsh : σ.sh src = 0) (hd : σ.sh dst = (σ.st dst).length) (hSC : σ.val SC = 0)
    (hcap : σ.val OP + 2 * (records.flatMap frame).length + 1 ≤ cap) :
    WExec cap (appendMarkedRecordsReset src dst OP SC) σ
      (appendO σ dst OP (marks (records.flatMap frame)))
      (100 * ((records.flatMap frame).length + 1)) := by
  have e1 := CounterAsm.frameLoop_spec cap hsd hOS
    (emits_pair (cap := cap) (dst := dst) (OP := OP)) (d := 2) (by intro b; simp)
    rest hend records [] σ hne (by simpa using hs) (by simpa using hsh) hd
    (by omega) (by rw [hSC]; omega)
  change WExec cap _ σ
    (adv src dst OP SC σ (marks (records.flatMap frame)) (records.flatMap frame).length) _ at e1
  let τ := adv src dst OP SC σ (marks (records.flatMap frame)) (records.flatMap frame).length
  have hlen : (records.flatMap frame).length ≤ cap := by omega
  have e2 := wrewind_spec cap src SC (records.flatMap frame).length τ
    (by simp [τ, adv, hSC]) (by simpa [τ, adv, hSC] using hlen)
  refine (e1.seq e2).cast cap ?_ (by omega)
  apply WState.eq
  · funext i
    by_cases hi : i = src
    · subst hi; simp [τ, adv, appendO, hsd, hsh]
    · simp [τ, adv, Function.update_of_ne hi]
  · rfl
  · funext i
    by_cases hi : i = SC
    · subst hi; simp [τ, adv, appendO, hOS.symm, hSC]
    · simp [τ, adv, Function.update_of_ne hi]
  · rfl

/-- `lem:print`, paper/paper.tex: a real
framed role reply is inserted into its new framed source record with
one marker per actual source bit and no supplied output length. -/
def appendMarkedFrameReset (src dst : Fin (ns + 1)) (OP SC : Fin nr) : WM ns nr :=
  .seq (CounterAsm.frameCopy src SC (fun b => emitPair dst OP b)) (WM.rewind src SC)

/-- `lem:print` and `prop:time`, paper/paper.tex: a single real frame is scanned, marked,
copied and rewound with its complete linear physical clock. -/
theorem appendMarkedFrameReset_spec (cap : ℕ) (src dst : Fin (ns + 1))
    (OP SC : Fin nr) (hsd : src ≠ dst) (hOS : OP ≠ SC)
    (bits rest : List Bool) (σ : WState ns nr)
    (hs : σ.st src = frame bits ++ rest) (hsh : σ.sh src = 0)
    (hd : σ.sh dst = (σ.st dst).length) (hSC : σ.val SC = 0)
    (hcap : σ.val OP + 2 * (frame bits).length + 1 ≤ cap) :
    WExec cap (appendMarkedFrameReset src dst OP SC) σ
      (appendO σ dst OP (marks (frame bits))) (100 * ((frame bits).length + 1)) := by
  have e1 := CounterAsm.frameCopy_spec cap hsd hOS
    (emits_pair (cap := cap) (dst := dst) (OP := OP)) (d := 2) (by intro b; simp)
    bits [] rest σ (by simpa using hs) (by simpa using hsh) hd (by omega) (by omega)
  change WExec cap _ σ
    (adv src dst OP SC σ (marks (frame bits)) (frame bits).length) _ at e1
  let τ := adv src dst OP SC σ (marks (frame bits)) (frame bits).length
  have hlen : (frame bits).length ≤ cap := by omega
  have e2 := wrewind_spec cap src SC (frame bits).length τ
    (by simp [τ, adv, hSC]) (by simpa [τ, adv, hSC] using hlen)
  refine (e1.seq e2).cast cap ?_ (by omega)
  apply WState.eq
  · funext i
    by_cases hi : i = src
    · subst hi; simp [τ, adv, appendO, hsd, hsh]
    · simp [τ, adv, Function.update_of_ne hi]
  · rfl
  · funext i
    by_cases hi : i = SC
    · subst hi; simp [τ, adv, appendO, hOS.symm, hSC]
    · simp [τ, adv, Function.update_of_ne hi]
  · rfl

end NearQuarticWires.StageNativeKids
