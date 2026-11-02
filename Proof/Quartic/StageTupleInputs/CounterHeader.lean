import Proof.Quartic.StagePrintTuple.InputContracts
import Proof.Wire_3_5.PrimAsmWriteNat
import Proof.Wire_3_5.FinalPassHashTable

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTupleInputs

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass.Hash4
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat

variable {ns nr : ℕ}

def writerBank (R : Fin 9↪Fin nr) : Fin 8↪Fin nr := Fin.castSuccEmb.trans R

/-- `lem:print`, paper/paper.tex: serialize a
physically computed persistent support counter through an actual
scratch copy, restoring the source and every writer scratch register. -/
def counterHeaderProgram (A : Fin nr) (R : Fin 9↪Fin nr) (dst : Fin (ns+1)) : WM ns nr :=
  .seq (wcopyR A (R 0) (R 6))
    (.seq (writeNatM dst (writerBank R)) (WM.clear (R 0)))

def counterHeaderCost (value : ℕ) : ℕ :=
  (natBitLength value+10)*(100*value+200)+21*value+6

/-- `lem:print` and `prop:time`, paper/paper.tex: actual numeric header writing uses only the small
persistent support counter and pays its complete copy/encoding/clear. -/
theorem counterHeaderProgram_spec (cap : ℕ) (A : Fin nr) (R : Fin 9↪Fin nr)
    (dst : Fin (ns+1)) (hA : ∀i,R i≠A) (σ : WState ns nr)
    (hz : ∀i:Fin 9,i.val<7→σ.val (R i)=0)
    (hd : σ.sh dst=(σ.st dst).length)
    (hcap : σ.val A+σ.val (R 7)+6*natBitLength (σ.val A)+6≤cap) :
    WExec cap (counterHeaderProgram A R dst) σ
      (appendO σ dst (R 7) (marks (natWord (σ.val A)))) (counterHeaderCost (σ.val A)) := by
  have hr {i j : Fin 9} : R i=R j↔i=j := R.injective.eq_iff
  have e1:=wcopyR_spec cap A (R 0) (R 6) (hA 0).symm (hA 6).symm
    (R.injective.ne (by decide)) σ (hz 0 (by decide)) (hz 6 (by decide)) (by omega)
  let d:=σ.setv (R 0) (σ.val A)
  have e2:=writeNatM_spec cap dst (writerBank R) d
    (by simp [d,writerBank,hr,hz 1 (by decide)])
    (by simp [d,writerBank,hr,hz 2 (by decide)])
    (by simp [d,writerBank,hr,hz 3 (by decide)])
    (by simp [d,writerBank,hr,hz 4 (by decide)])
    (by simp [d,writerBank,hr,hz 5 (by decide)])
    (by simp [d,writerBank,hr,hz 6 (by decide)])
    (by simpa only [d,WState.setv_sh,WState.setv_st] using hd)
    (by simpa [d,writerBank,hr] using hcap)
  let e:=appendO d dst (R 7) (marks (natWord (σ.val A)))
  have dv : d.val ((writerBank R) 0)=σ.val A := by simp [d,writerBank]
  rw [dv] at e2
  have e3:=wclear_spec cap (R 0) (σ.val A) e
    (by simp [e,d,appendO,hr]) (by simp [e,d,appendO,hr];omega)
  refine (e1.seq (e2.seq e3)).cast cap ?_ ?_
  · apply WState.eq
    · rfl
    · rfl
    · funext i
      by_cases hi : i=R 0
      · subst i;simp [e,d,appendO,hr,hz 0 (by decide)]
      · by_cases hi7 : i=R 7
        · subst i;simp [e,d,appendO,hr]
        · simp [e,d,appendO,Function.update_of_ne hi,Function.update_of_ne hi7]
    · rfl
  · simp only [counterHeaderCost,d,writerBank,Function.Embedding.trans_apply,
      Fin.coe_castSuccEmb,WState.setv_val,Function.update_self]
    omega

end NearQuarticWires.StageTupleInputs
