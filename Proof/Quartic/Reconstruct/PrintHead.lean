import Proof.Quartic.Reconstruct.PrintInput

/-!
# Reading the input of the printing stage

Paper: Step 3 of `sec:algorithm`, paper/paper.tex.

`printHeadS` reads `gammaWord q` once (`printHeadS_spec`): the call and the parameters, counting their bits
(`scanCallS`, `scanParamsS`), keeping the scalars it needs and the primes and the rates; it computes `2mG_j` and the
length of `prepWord` (`wpLenS`, kept in `kPL`), moves back to the start, copies `prepWord` into store `sP`, and copies the framed
certified bits, the framed seed prefix and the framed coefficient table into the stores `sZ`, `sX`, `sG`.
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces (callWord kindTag listWord)
open NearCubicWires.RepairOrdinary (frame)
open NearQuarticWires.Greedy NearQuarticWires.Program
open NearQuarticWires.StageMain.CallSkip

variable {C : Ctx} {B1 B2 : ℕ}

/-- The store of the bits of `prepWord`. -/
def sP : Fin MM := ⟨5, by decide⟩
/-- The store of the bits of the framed coefficient table. -/
def sG : Fin MM := ⟨6, by decide⟩
/-- A scratch store (the framed seed prefix). -/
def sX : Fin MM := ⟨7, by decide⟩

/-- Read the input of the printing stage. -/
def printHeadS : St VV MM :=
  .seq scanCallS (.seq scanParamsS (.seq wpLenS (.seq (rewindS kR) (.seq (.op (.copy kR kPL)) (.seq (rawCopyS sP kR)
    (.seq (rawFrameS sZ) (.seq (rawFrameS sX) (rawFrameS sG))))))))

/-- The stores written by `printHeadS`. -/
def headStores : List (Fin MM) := [sPr, sF, sP, sZ, sX, sG]

/-- The cost of `printHeadS`. -/
noncomputable def printHeadCost (q : ChildRequest B1 B2) : ℕ :=
  scanCallCost (callWord q.call).length + scanParamsCost (parametersWord q.selected.1).length + 48 +
    (gammaWord q).length * 12 + 12 * ((gammaWord q).length + 3) + 30

/-- The state after `printHeadS`. -/
structure HeadDone (q : ChildRequest B1 B2) (b : DS VV MM) : Prop where
  n : b.env kN = q.call.n
  kind : b.env kKd = kindTag q.call.kind
  k : b.env kK = q.selected.1.k
  hE : b.env kE = q.selected.1.hE
  m1 : b.env kM = q.selected.1.M1
  jj : b.env kJ1 = q.selected.1.J
  aa : b.env kA = q.selected.1.A
  lam : b.env kL = q.selected.1.Lambda
  b0 : b.env kB0 = 2 * Algorithm.traceOrder * Builder.occurrences q.call 0
  b1 : b.env kB1 = 2 * Algorithm.traceOrder * Builder.occurrences q.call 1
  pr : b.ram sPr = q.selected.1.primes.sort (· ≤ ·)
  npr : b.env kPc = (q.selected.1.primes.sort (· ≤ ·)).length
  fs : b.ram sF = q.selected.1.factors
  pw : b.ram sP = (prepWord B1 B2 q.call q.witness).map Bool.toNat
  zb : b.ram sZ = (frame (certifiedBits q.cellCall)).map Bool.toNat
  gt : b.ram sG = (gammaTableWord q).map Bool.toNat
  rcs : ∀ m ∈ headStores, b.rc m = (b.ram m).length
  rest : ∀ m, m ∉ headStores → b.ram m = [] ∧ b.rc m = 0
  ip : b.ip = (gammaWord q).length
  cst : Cst b
  pl : b.env kPL = (prepWord B1 B2 q.call q.witness).length

end NearQuarticWires.Reconstruct
