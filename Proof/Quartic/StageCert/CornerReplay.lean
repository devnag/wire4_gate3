import Proof.Quartic.StageCert.CornerGate
import Proof.Gates.Dispatch.WitnessB

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicWires
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces
open NearQuarticWires.StageMain

/-- `sec:cells`, paper/paper.tex: the original gate's
source offset is retained across its four literal corner evaluations. -/
def cornerGateStart : Fin VV := ⟨124,by decide⟩

/-- `sec:cells`, paper/paper.tex: each corner rereads the
same original encoded raw gate, after a paid source-cursor rewind. -/
def replayCorner (l : Fin 4) : St VV := .seq (seekW cornerGateStart) (scoreCorner l)

/-- `sec:cells`, paper/paper.tex: the cursor rewind adds
only the literal source-bit register to the corner evaluator's frame. -/
def replayCornerScratch (l : Fin 4) : List (Fin VV) :=
  t0::vPOS::vJ::scoreCornerScratch l

/-- `sec:cells` and `prop:time`, paper/paper.tex: repeated corner evaluation scans the actual original source
word and retains the exact signed threshold convention. -/
theorem replayCorner_run (C : Ctx) {n : ℕ} (g : NormalizedThresholdGate n)
    (l : Fin 4) (a : DS VV) (hc : Cst a) (rest : List Bool)
    (base : ℕ) (hbase : a.env cornerGateStart=base)
    (hin : C.cw.drop base=gateWord g++rest) (hbl : base≤C.cw.length)
    (hW : C.cw.length+3≤C.Wd) (hpoint : a.env (cornerPoint l)<2^C.Wd) :
    Hs C (replayCorner l) a (210*(C.cw.length+2)^2+4) (fun z =>
      z.env (cornerBit l)=(g.eval (packedPoint n (a.env (cornerPoint l)))).toNat ∧
      z.cp=base+(gateWord g).length ∧ z.wq=a.wq ∧ z.out=a.out ∧ Cst z ∧
      FrS a z (replayCornerScratch l)) := by
  have hL : C.cw.length<2^C.Wd := by
    have h := Nat.lt_two_pow_self (n := C.Wd)
    omega
  unfold replayCorner
  apply Hx.hs
  refine Hs.then (seekW_spec cornerGateStart (by decide) (by decide) a hc base hbase hbl hL)
    (fun r ⟨rc,rw,ro,rconst,rf⟩ n1 hn1 => ?_)
  have rp : r.env (cornerPoint l)=a.env (cornerPoint l) :=
    rf _ (by fin_cases l <;> decide)
  refine Hs.last (scoreCorner_run C g l r rconst rest (by rw [rc]; exact hin) hW
    (by rw [rp]; exact hpoint))
    (fun z ⟨zb,zc,zw,zo,zconst,zfr⟩ n2 hn2 => ?_)
  refine ⟨⟨by simpa only [rp] using zb,by rw [zc,rc],zw.trans rw,zo.trans ro,zconst,?_⟩,?_⟩
  · exact (rf.toS.weaken (by simp [replayCornerScratch])).trans
      (zfr.weaken (by intro y hy; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ hy))))
  · have hp : C.cw.length+2≤(C.cw.length+2)^2 := Nat.le_self_pow (by decide) _
    nlinarith only [hn1,hn2,hbl,hp]

end NearQuarticWires.StageCert
