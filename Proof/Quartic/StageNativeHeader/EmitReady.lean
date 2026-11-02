import Proof.Quartic.StageNativeHeader.Regs

/-!
# The state before the emission of the native table request

Paper: `lem:print`, paper/paper.tex.

After the five fields are read, the column field is computed by the column printer and the cuts are counted, the
state satisfies `EmitReady r`: the input stream is positioned at the marked cut bytes, the column field
`frame (colsContent P)` is on `sY`, the registers hold `n, r, b, s, p`, the dense width, `(r/2)·s`, `d`, the stride
and the cut count, and every other register is `0`. The emission (`emitP`) then writes `marks (table.word)` on the
accumulator `sACC`, its head back at `0`, within `emitCost r` steps for every capacity of at least `emitCap r`.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageNativeHeader

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearQuarticWires.StagePrint NearQuarticWires.StagePrint.Downstream

/-- The register of the cut count. -/
def rG : Fin hnr := 36

/-- The registers of the final copy (left at `0` by the emission). -/
def rFO : Fin hnr := 52
def rFC : Fin hnr := 53

/-- The registers holding values before the emission. -/
def keptRegs : List (Fin hnr) := [rN, rR, rB, rS, rP, rW, rM, rD, rT2, rG]

/-- The five fields of the input. -/
def fieldsWord (r : NativeHeaderRequest) : List Bool :=
  [r.parameters.n, r.parameters.r, r.parameters.b, r.parameters.s, r.table.matrix.p].flatMap natWord

theorem word_eq (r : NativeHeaderRequest) : r.word = fieldsWord r ++ r.stream := rfl

/-- **The state before the emission.** -/
structure EmitReady (r : NativeHeaderRequest) (σ : WState hns hnr) : Prop where
  inp : σ.st sIN = marks (fieldsWord r) ++ marks r.stream ++ [false]
  inph : σ.sh sIN = (marks (fieldsWord r)).length
  cols : σ.st sY = frame (colsContent r.parameters)
  colsh : σ.sh sY = 0
  acc : σ.st sACC = []
  acch : σ.sh sACC = 0
  zd : σ.st sZd = []
  zdh : σ.sh sZd = 0
  zp : σ.st sZp = []
  zph : σ.sh sZp = 0
  zg : σ.st sZG = []
  zgh : σ.sh sZG = 0
  vN : σ.val rN = r.parameters.n
  vR : σ.val rR = r.parameters.r
  vB : σ.val rB = r.parameters.b
  vS : σ.val rS = r.parameters.s
  vP : σ.val rP = r.table.matrix.p
  vW : σ.val rW = PrimT.C4Geo.width r.parameters
  vM : σ.val rM = r.parameters.r / 2 * r.parameters.s
  vD : σ.val rD = PrimT.C4Geo.dRow r.parameters
  vT2 : σ.val rT2 = 2 * PrimT.C4Geo.width r.parameters + 2
  vG : σ.val rG = r.table.matrix.cuts.length
  zero : ∀ x, x ∉ keptRegs → σ.val x = 0

/-- The capacity available to the emission. -/
def emitCap (r : NativeHeaderRequest) : ℕ :=
  1000 * (r.word.length + (frame r.table.word).length + r.table.count + 100)

/-- The step bound of the emission: linear in the cut bytes and the `U²` count, polynomial in `n, p`. -/
def emitCost (r : NativeHeaderRequest) : ℕ :=
  10 ^ 12 * (r.parameters.n + r.table.matrix.p + 2) ^ 4 * (r.stream.length + r.table.count + 1)

end NearQuarticWires.StageNativeHeader
