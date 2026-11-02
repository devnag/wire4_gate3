import Proof.Quartic.StageNativeKids.RoleInput

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKids

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.WordPrograms
open StageTuple

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: after
literal role-source assembly, the actual written-cell counter rewinds
the callee's input and clears itself before ordinary execution. -/
def roleSourceReadyProgram (P : Fin 4 ↪ Fin (ns + 1)) (OP SC K : Fin nr) : WM ns nr :=
  .seq (roleSourceInputProgram P OP SC K) (WM.rewind (P 3) OP)

/-- `prop:time`, paper/paper.tex: the
complete role handoff pays its binary source copies and final rewind. -/
def roleSourceReadyCost (base : List Bool) (context : List ℕ) (atom : ℕ) : ℕ :=
  roleSourceInputCost base context atom +
    6 * (frame (base ++ context.flatMap natWord ++ natWord atom)).length + 10

/-- `lem:print` and `prop:time`, paper/paper.tex: the exact role input is acquired on a real
empty callee tape, while every retained source, cursor and register is
unchanged at the ordinary-call boundary. -/
theorem roleSourceReadyProgram_spec (cap : ℕ) (P : Fin 4 ↪ Fin (ns + 1))
    (OP SC K : Fin nr) (hOS : OP ≠ SC) (hKO : K ≠ OP) (hKS : K ≠ SC)
    (base : List Bool) (context : List ℕ) (atom : ℕ) (hcount : context.length = 4)
    (restB restC restA : List Bool) (σ : WState ns nr)
    (hb : σ.st (P 0) = frame base ++ restB)
    (hc : σ.st (P 1) = context.flatMap natWord ++ restC)
    (ha : σ.st (P 2) = natWord atom ++ restA)
    (hh : ∀ i : Fin 4, σ.sh (P i) = 0)
    (hd : σ.st (P 3) = []) (ho : σ.val OP = 0)
    (hSC : σ.val SC = 0) (hK : σ.val K = 0)
    (hcap : 2 * (base.length + (context.flatMap natWord).length + (natWord atom).length) + 3 ≤ cap) :
    WExec cap (roleSourceReadyProgram P OP SC K) σ
      (σ.sets (P 3) (frame (base ++ context.flatMap natWord ++ natWord atom)))
      (roleSourceReadyCost base context atom) := by
  let bytes := frame (base ++ context.flatMap natWord ++ natWord atom)
  have e1 := roleSourceInputProgram_spec cap P OP SC K hOS hKO hKS
    base context atom hcount restB restC restA σ hb hc ha hh hd ho hSC hK hcap
  let τ := appendO σ (P 3) OP bytes
  have e2 := wrewind_spec cap (P 3) OP bytes.length τ
    (by simp [τ, appendO, ho])
    (by simp only [τ, appendO_val, Function.update_self, ho, Nat.zero_add]
        simpa only [bytes, NearCubicWires.RepairOrdinary.frame_length, List.length_append] using
          (show 2 * (base.length + (context.flatMap natWord).length + (natWord atom).length) + 1 ≤ cap by omega))
  refine (e1.seq e2).cast cap ?_ (by unfold roleSourceReadyCost; dsimp only [bytes]; omega)
  apply WState.eq
  · funext i
    by_cases hi : i = P 3
    · subst hi
      simp [τ, appendO, ho, hh]
    · simp [τ, appendO, hi]
  · simp [τ, appendO, hd, bytes]
  · funext i
    by_cases hi : i = OP
    · subst hi
      simp [τ, appendO, ho]
    · simp [τ, appendO, hi]
  · rfl

end NearQuarticWires.StageNativeKids
