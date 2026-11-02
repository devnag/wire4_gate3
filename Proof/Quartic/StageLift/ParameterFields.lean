import Proof.Quartic.StageLift.Fields
import Proof.Quartic.Program.Stages

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces

/-- `sec:params`, paper/paper.tex: signed natural
fields of the original integer input codec. -/
def integerFields (z : ℤ) : List ℕ := [if z < 0 then 1 else 0, z.natAbs]

/-- `sec:params`, paper/paper.tex: every rational
retains its actual sign, numerator magnitude, and positive denominator. -/
def rationalFields (q : ℚ) : List ℕ := integerFields q.num ++ [q.den]

/-- `sec:params`, paper/paper.tex: scalar fields
preceding the actual prime-list length header. -/
def parameterHeadScalars (p : Cells.Parameters) : List ℕ :=
  [p.lambda, p.mu, p.m, p.r, p.s, p.b, p.k, p.N, p.Jmax, p.T, p.tau, p.U,
    p.Xmax, p.dstar, p.omega1, p.omega2, p.MF, p.Q, p.ellf, p.S, p.NatAtoms,
    p.childCap, p.Uocc, p.Dmax, p.BN, p.P, p.e, p.hE, p.h, p.Lw] ++
    rationalFields p.pi0 ++ rationalFields p.eta ++ [p.Qexp]

/-- `sec:params`, paper/paper.tex: exact natural
header fields before the sorted prime payload. -/
def parameterHeadFields (p : Cells.Parameters) : List ℕ :=
  parameterHeadScalars p ++ [p.primes.card]

/-- `sec:params`, paper/paper.tex: scalar fields
between the prime payload and the actual factor-list length. -/
def parameterTailScalars (p : Cells.Parameters) : List ℕ :=
  [p.Dprime, p.L2, p.M1, p.J, p.A, p.Lambda] ++ rationalFields p.ell0

/-- `sec:params`, paper/paper.tex: exact natural
header fields after the prime payload and before the factor payload. -/
def parameterTailFields (p : Cells.Parameters) : List ℕ :=
  parameterTailScalars p ++ [p.factors.length]

/-- `sec:params`, paper/paper.tex: the scalar
header count includes every rational sign and denominator field. -/
theorem parameterHeadFields_length (p : Cells.Parameters) :
    (parameterHeadFields p).length = 38 := by
  simp [parameterHeadFields, parameterHeadScalars, rationalFields, integerFields]

/-- `sec:params`, paper/paper.tex: the exact
scalar tail has ten natural-codec fields. -/
theorem parameterTailFields_length (p : Cells.Parameters) :
    (parameterTailFields p).length = 10 := by
  simp [parameterTailFields, parameterTailScalars, rationalFields, integerFields]

/-- `sec:params`, paper/paper.tex: thirty-seven
scalar header fields precede the prime-list length itself. -/
theorem parameterHeadScalars_length (p : Cells.Parameters) :
    (parameterHeadScalars p).length = 37 := by
  simp [parameterHeadScalars, rationalFields, integerFields]

/-- `sec:params`, paper/paper.tex: nine scalar
tail fields precede the factor-list length itself. -/
theorem parameterTailScalars_length (p : Cells.Parameters) :
    (parameterTailScalars p).length = 9 := by
  simp [parameterTailScalars, rationalFields, integerFields]

/-- `sec:params`, paper/paper.tex: the complete
physical parameter reader consumes exactly the public stage codec,
without assuming that the input parameters are already decoded. -/
theorem parametersWord_field_layout (p : Cells.Parameters) :
    Program.parametersWord p = (parameterHeadFields p).flatMap natWord ++
      (p.primes.sort (· ≤ ·)).flatMap natWord ++ (parameterTailFields p).flatMap natWord ++
      p.factors.flatMap natWord := by
  simp [Program.parametersWord, parameterHeadFields, parameterTailFields,
    parameterHeadScalars, parameterTailScalars, rationalFields,
    integerFields, ratWord, NearCubicGates.Close.Interfaces.intWord, listWord, List.append_assoc]

/-- `sec:params`, paper/paper.tex: fixed scalar
blocks and self-counted lists form the literal whole parameter word. -/
theorem parametersWord_block_layout (p : Cells.Parameters) :
    Program.parametersWord p = (parameterHeadScalars p).flatMap natWord ++
      listWord natWord (p.primes.sort (· ≤ ·)) ++ (parameterTailScalars p).flatMap natWord ++
      listWord natWord p.factors := by
  rw [parametersWord_field_layout]
  simp [parameterHeadFields, parameterTailFields, listWord, List.append_assoc]

end NearQuarticWires.StageLift
