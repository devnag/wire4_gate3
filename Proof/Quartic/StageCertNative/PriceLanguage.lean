import Proof.Quartic.StageCertNative.PriceBasic
import Proof.Quartic.StageMain.CompilerRuntime

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells

/-- `prop:time`, paper/paper.tex: a fixed
original-arity binary allocation contributes a polynomial multiplier
to the actual source work and source length. -/
theorem JobPrice.language {B1 B2 : ℕ}
    {input : TermJob B1 B2→List Bool} {steps : TermJob B1 B2→ℕ} {d : ℕ}
    (hi : JobPrice (fun r=>(input r).length) d) (hs : JobPrice steps d)
    (K : Callee) (z : Sz) (V M : ℕ)
    (hh : JobPrice (fun r=>leadOnes (input r)) 0)
    (hw : JobPrice (fun r=>z.W (leadOnes (input r))) 0)
    (hl : JobPrice (fun r=>z.Lk (leadOnes (input r))) 0)
    (hb : JobPrice (fun r=>z.Bk (leadOnes (input r))) 0) :
    JobPrice (fun r=>langBudget K z V M (input r) (steps r)) d := by
  let S : TermJob B1 B2→ℕ:=fun r=>leadOnes (input r)+z.W (leadOnes (input r))+
    z.Lk (leadOnes (input r))+z.Bk (leadOnes (input r))+
    (V+M+TSK K+z.a1+z.c1+z.a2+z.c2+z.a3+z.c3+1)
  have hS : JobPrice S 0 := (((hh.add hw).add hl).add hb).add
    (JobPrice.constant (V+M+TSK K+z.a1+z.c1+z.a2+z.c2+z.a3+z.c3+1))
  have hp0 : JobPrice (fun r=>10000*S r^2) 0 :=
    (JobPrice.constant 10000).mul (hS.pow 2)
  have hp:=hp0.mul ((hs.add hi).add ((JobPrice.constant 1).raise (Nat.zero_le d)))
  have hp' : JobPrice (fun r=>10000*S r^2*(steps r+(input r).length+1)) d := by
    simpa only [zero_add] using hp
  refine hp'.mono ?_
  intro r
  apply StageMain.Runtime.langBudget_le K z V M (input r) (steps r) (S r)
  all_goals dsimp only [S];omega

end NearQuarticWires.StageCertNative
