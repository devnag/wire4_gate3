import Proof.Quartic.StagePrintTuple.PayloadCopy

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.Recovery.HTParts

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: a fixed number
of actual natural-codec fields is copied without evaluating their
possibly exponential numeric values. The scan counter records bytes. -/
def copyNaturalFields (count : ℕ) (src dst : Fin (ns+1)) (OP SC K : Fin nr) : WM ns nr :=
  match count with
  | 0 => WM.skip
  | count+1 => .seq (CounterAsm.natCopy src SC K (fun b=>emitPair dst OP b))
      (copyNaturalFields count src dst OP SC K)

/-- `lem:print` and `prop:time`, paper/paper.tex: the fixed-field copier advances through exactly the
actual binary source fields and appends only their marked bytes. -/
theorem copyNaturalFields_spec (cap : ℕ) (src dst : Fin (ns+1)) (OP SC K : Fin nr)
    (hsd : src≠dst) (hOS : OP≠SC) (hKO : K≠OP) (hKS : K≠SC) :
    ∀ (values : List ℕ) (pre rest : List Bool) (σ : WState ns nr),
      σ.st src=pre++values.flatMap natWord++rest → σ.sh src=pre.length →
      σ.sh dst=(σ.st dst).length → σ.val K=0 →
      σ.val OP+2*(values.flatMap natWord).length≤cap →
      σ.val SC+(values.flatMap natWord).length<cap+1 →
      WExec cap (copyNaturalFields values.length src dst OP SC K) σ
        (adv src dst OP SC σ (marks (values.flatMap natWord))
          (values.flatMap natWord).length)
        (28*(values.flatMap natWord).length+values.length) := by
  intro values
  induction values with
  | nil =>
    intro pre rest σ _hs _hh _hd _hk _hc _hsc
    simpa [copyNaturalFields,marks,adv_zero] using (WExec.skip (cap:=cap) σ)
  | cons v values ih =>
    intro pre rest σ hs hh hd hk hc hsc
    have hlen : ((v::values).flatMap natWord).length=
      (natWord v).length+(values.flatMap natWord).length := by simp
    have e1 := CounterAsm.natCopy_spec cap hsd hOS hKO hKS
      (emits_pair (cap:=cap) (dst:=dst) (OP:=OP)) (d:=2) (by intro b;simp)
      v pre (values.flatMap natWord++rest) σ
      (by simpa only [List.flatMap_cons,List.append_assoc] using hs) hh hd hk
      (by rw [hlen] at hc;omega) (by rw [hlen] at hsc;omega)
      (by rw [hlen] at hsc;omega)
    have hm : (natWord v).flatMap (fun b=>[true,b])=marks (natWord v) := rfl
    rw [hm] at e1
    let d := adv src dst OP SC σ (marks (natWord v)) (natWord v).length
    have e2 := ih (pre++natWord v) rest d
      (by rw [show d=adv src dst OP SC σ (marks (natWord v)) (natWord v).length from rfl,
        adv_st_src hsd,hs];simp only [List.flatMap_cons,List.append_assoc])
      (by simp [d,adv_sh_src,hh])
      (by rw [show d=adv src dst OP SC σ (marks (natWord v)) (natWord v).length from rfl,
        adv_sh_dst hsd,adv_st_dst];simp [hd])
      (by rw [show d=adv src dst OP SC σ (marks (natWord v)) (natWord v).length from rfl,
        adv_val_other _ _ _ K hKO hKS,hk])
      (by rw [show d=adv src dst OP SC σ (marks (natWord v)) (natWord v).length from rfl,
        adv_val_OP hOS];simp only [Codec.marks_length];rw [hlen] at hc;omega)
      (by rw [show d=adv src dst OP SC σ (marks (natWord v)) (natWord v).length from rfl,
        adv_val_SC];rw [hlen] at hsc;omega)
    refine (e1.seq e2).cast cap ?_ (by
      simp only [List.flatMap_cons,List.length_append,List.length_cons]
      omega)
    rw [show d=adv src dst OP SC σ (marks (natWord v)) (natWord v).length from rfl,
      adv_adv hsd hOS]
    simp only [List.flatMap_cons,List.length_append,Streaming.marks_append]

end NearQuarticWires.StageTuple
