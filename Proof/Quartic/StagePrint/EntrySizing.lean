import Proof.Quartic.StagePrint.EntryMemory

set_option autoImplicit false

namespace NearQuarticWires.StagePrint.EntryFormat

open NearCubicWires NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: one original
arity polynomial bounds binary header heights, the logarithm of the
actual finite stream length, and the exact packing arithmetic. -/
noncomputable def Request.sizingMagnitude {modular : Bool} (r : Request modular) : ℕ :=
  let n:=r.header.call.n
  let L:=r.toRowContext.nativeFieldWidth
  4*(n+1)^2+n+20+
    ((r.degree+2)*(L+2*((n+1)/2)+r.degree+4)+r.coefficientBits+n+L+r.degree+30)+
    natBitLength r.word.length+natBitLength r.scale+
    natBitLength r.walkCode.val+natBitLength r.degree+100

/-- `lem:print` and `prop:time`, paper/paper.tex: fixed source bounds are mathematical guarantees only;
the literal input remains the same original-arity-first word. -/
structure BoundedRequest (C E : ℕ) (modular : Bool) extends Request modular where
  size_bound : toRequest.sizingMagnitude≤C*(header.call.n+1)^E

/-- `lem:print`, paper/paper.tex: no bound,
stream length, source width or decoded field is added to the runtime
input when the selected original-arity estimate is applied. -/
def BoundedRequest.word {C E : ℕ} {modular : Bool} (r : BoundedRequest C E modular) : List Bool :=
  r.toRequest.word

end NearQuarticWires.StagePrint.EntryFormat
