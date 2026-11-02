import Proof.Quartic.StagePrintTuple.NaturalsCopy

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Recovery.HTParts

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: a fixed scalar
context is copied as encoded bytes and its actual source cursor is
reset using the number of scanned cells, not its numeric values. -/
def appendNaturalsReset (count : ℕ) (src dst : Fin (ns+1)) (OP SC K : Fin nr) : WM ns nr :=
  .seq (copyNaturalFields count src dst OP SC K) (WM.rewind src SC)

/-- `prop:time`, paper/paper.tex: both the
actual fixed-field copy and its literal cell-by-cell rewind are paid. -/
def appendNaturalsCost (values : List ℕ) : ℕ :=
  60*((values.flatMap natWord).length+1)+values.length

/-- `lem:print` and `prop:time`, paper/paper.tex: one fixed actual scalar context is retained after its
marked bytes are appended; all scratch and source cursors are reset. -/
theorem appendNaturalsReset_spec (cap : ℕ) (src dst : Fin (ns+1)) (OP SC K : Fin nr)
    (hsd : src≠dst) (hOS : OP≠SC) (hKO : K≠OP) (hKS : K≠SC)
    (values : List ℕ) (rest : List Bool) (σ : WState ns nr)
    (hs : σ.st src=values.flatMap natWord++rest) (hsh : σ.sh src=0)
    (hd : σ.sh dst=(σ.st dst).length) (hSC : σ.val SC=0) (hK : σ.val K=0)
    (hcap : σ.val OP+2*(values.flatMap natWord).length+1≤cap) :
    WExec cap (appendNaturalsReset values.length src dst OP SC K) σ
      (appendO σ dst OP (marks (values.flatMap natWord))) (appendNaturalsCost values) := by
  have e1 := copyNaturalFields_spec cap src dst OP SC K hsd hOS hKO hKS
    values [] rest σ (by simpa using hs) (by simpa using hsh) hd hK
    (by omega) (by rw [hSC];omega)
  let τ := adv src dst OP SC σ (marks (values.flatMap natWord))
    (values.flatMap natWord).length
  have hlen : (values.flatMap natWord).length≤cap := by omega
  have e2 := wrewind_spec cap src SC (values.flatMap natWord).length τ
    (by simp only [τ,adv,WState.setv_val,Function.update_self,hSC,Nat.zero_add])
    (by simpa only [τ,adv,WState.setv_val,Function.update_self,hSC,Nat.zero_add] using hlen)
  refine (e1.seq e2).cast cap ?_ (by unfold appendNaturalsCost;omega)
  apply WState.eq
  · funext i
    by_cases hi : i=src
    · subst hi
      simp [τ,adv,appendO,hsd,hsh]
    · simp [τ,adv,Function.update_of_ne hi]
  · rfl
  · funext i
    by_cases hi : i=SC
    · subst hi
      simp [τ,adv,appendO,hOS.symm,hSC]
    · simp [τ,adv,Function.update_of_ne hi]
  · rfl

end NearQuarticWires.StageTuple
