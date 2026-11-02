import Proof.Quartic.StageCert.FourCorners
import Proof.Quartic.StageCert.DeltaBits

set_option autoImplicit false

namespace NearQuarticWires.StageCert
open NearCubicWires
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces
open NearQuarticWires.StageMain

/-- `sec:cells`, paper/paper.tex: evaluate the actual raw
gate at the four original points, then compute its signed mixed difference
and exact population magnitude. -/
def deltaGate : St VV := .seq fourCorners deltaBits

/-- `sec:cells`, paper/paper.tex: one mixed-difference
evaluation retains all four packed original points and all external fields. -/
def deltaGateScratch : List (Fin VV) :=
  deltaPositive::deltaNegative::deltaMagnitude::fourCornerScratch

/-- `sec:cells` and `prop:time`, paper/paper.tex: a mixed residual occurrence is computed directly from its
original gate word, including every signed value and inclusive tie. -/
theorem deltaGate_run (C : Ctx) {n : ℕ} (g : NormalizedThresholdGate n)
    (a : DS VV) (hc : Cst a) (rest : List Bool)
    (hin : C.cw.drop a.cp=gateWord g++rest) (hbase : a.cp≤C.cw.length)
    (hW : C.cw.length+3≤C.Wd) (hpoint : ∀l,a.env (cornerPoint l)<2^C.Wd) :
    Hs C deltaGate a (860*(C.cw.length+2)^2+50) (fun z =>
      z.env deltaPositive=
        (g.eval (packedPoint n (a.env (cornerPoint 0)))).toNat+
        (g.eval (packedPoint n (a.env (cornerPoint 3)))).toNat ∧
      z.env deltaNegative=
        (g.eval (packedPoint n (a.env (cornerPoint 1)))).toNat+
        (g.eval (packedPoint n (a.env (cornerPoint 2)))).toNat ∧
      z.env deltaMagnitude=
        (fourBitDifference (fun l=>g.eval (packedPoint n (a.env (cornerPoint l))))).natAbs ∧
      z.cp=a.cp+(gateWord g).length ∧ z.wq=a.wq ∧ z.out=a.out ∧ Cst z ∧
      FrS a z deltaGateScratch) := by
  unfold deltaGate
  apply Hx.hs
  refine Hs.then (fourCorners_run C g a hc rest hin hbase hW hpoint)
    (fun b ⟨bb,bc,bw,bo,bconst,bfr⟩ n1 hn1 => ?_)
  have hf : 2<2^C.Wd := by
    have h := Nat.lt_two_pow_self (n := C.Wd)
    omega
  refine Hs.last (deltaBits_run C b bconst _ bb hf)
    (fun z ⟨zp,zn,zm,zc,zw,zo,zconst,zfr⟩ n2 hn2 => ?_)
  refine ⟨⟨zp,zn,zm,zc.trans bc,zw.trans bw,zo.trans bo,zconst,?_⟩,?_⟩
  · exact (bfr.weaken (by decide)).trans (zfr.toS.weaken (by decide))
  · omega

end NearQuarticWires.StageCert
