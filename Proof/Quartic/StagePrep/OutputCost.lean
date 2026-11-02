import Proof.Quartic.StagePrep.SuccessOutput
import Proof.Quartic.StagePrep.PrefixBudget

/-!
# The successful preparation writer has an original-call clock

Paper: the complete record in `sec:params`, paper/paper.tex, and `prop:time`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StagePrep

open NearCubicGates.Close.Dispatch
open NearCubicGates.Close.Counter
open NearCubicGates.Close.Interfaces

/-- The complete successful serializer and bounded-prefix work
of `prop:time`, paper/paper.tex. -/
def successOutputCost (c : Call) (p : Cells.Parameters) (Wd : ℕ) : ℕ :=
  (callWord c).length*8 + parameterWriterCost p.P (Jmax c.n) p.h Wd +
    10*Program.witnessReadLength c p+100

/-- The explicit successful-output envelope of `prop:time`,
paper/paper.tex, charges all scalar, prime,
factor and bounded witness-bit writes. -/
def successOutputMajorant (L Wd : ℕ) : ℕ :=
  L*8+parameterWriterCost L (L+1) L Wd+50*(L+1)^5+100

/-- The selected serializer charge of `prop:time`,
paper/paper.tex, is bounded by the literal
original-call output envelope, including its repeated chain. -/
theorem successOutputCost_le (c : Call) (p : Cells.Parameters)
    (hs : Cells.ParameterRules (Builder.callInput c) p) (L Wd : ℕ)
    (hn : c.n ≤ L) (hL : (callWord c).length ≤ L) :
    successOutputCost c p Wd ≤ successOutputMajorant L Wd := by
  have hP : p.P ≤ L := hs.prime_candidate.2.1.trans hn
  have hh : p.h ≤ L := by
    rw [hs.h_eq,hs.hE_eq]
    exact (Nat.div_le_self _ _).trans ((Nat.div_le_self _ _).trans hP)
  have hmu : p.mu ≤ c.n := hs.mu_le_lambda.trans (Cells.CoreRules.lambda_le_n (hs : Cells.CoreRules (Builder.callInput c) p))
  have hJ : Jmax c.n ≤ L+1 := by
    change NearCubicGates.Target.mu c.n+1 ≤ L+1
    have hme : p.mu=NearCubicGates.Target.mu c.n := hs.mu_eq
    rw [←hme]
    omega
  have hwriter : parameterWriterCost p.P (Jmax c.n) p.h Wd ≤ 
      parameterWriterCost L (L+1) L Wd := by
    unfold parameterWriterCost prPrintCost chainCost bodyCost
    gcongr
  have hread := (witnessReadLength_preparation_bound c p hs).trans
    (Nat.mul_le_mul_left 5 (Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) 5))
  unfold successOutputCost successOutputMajorant
  nlinarith only [hwriter,hread,hL]

/-- The physical output envelope in `prop:time`,
paper/paper.tex, is a polynomial of the original
call length at the fixed native register width. -/
theorem successOutputMajorant_poly (K : ℕ) :
    PolyB (fun L => successOutputMajorant L (wdOf K L)) := by
  unfold successOutputMajorant parameterWriterCost prPrintCost chainCost bodyCost pvCost wdOf
  polyb

end NearQuarticWires.StagePrep
