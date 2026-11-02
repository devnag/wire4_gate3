import Proof.Quartic.StagePrintTuple.TermsState
import Proof.Quartic.StagePrintTuple.KernelLayout
import Proof.Quartic.StageNativeKids.Request

set_option autoImplicit false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close.WordPrograms

/-- `prop:time`, paper/paper.tex: structural
size contains only original source/metadata, dimensions, degree and the
original child cap. It excludes all Terms bytes and the Terms count. -/
def TermCutRequest.censusMagnitude (r : TermCutRequest) (mc : ℕ) : ℕ :=
  r.setupStructuralMagnitude+r.rowDimension+r.degree+
    17*(Builder.allGates r.header.call).length+mc+1

/-- `prop:time`, paper/paper.tex: the actual
native source printer has one uniform polynomial budget in its finite
original input, original dimension and output field width. -/
def NativeStagePrice (B : StageNativeKids.NativeKidsRequest→ℕ) : Prop :=
  ∃ K E : ℕ,1 ≤ K ∧ 1 ≤ E ∧ ∀ r,
    B r ≤ K*(r.word.length+r.header.call.n+r.outputWidth+1)^E

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual fixed monomial subprogram acts directly
on the retained source state and charges its own support's original
child-choice square. This is an internal assembly record whose public
printer consumer instantiates the concrete source implementation. -/
structure TermStageMachine {B : StageNativeKids.NativeKidsRequest→ℕ}
    (native : WordFunction StageNativeKids.NativeKidsRequest StageNativeKids.NativeKidsRequest.word
      StageNativeKids.NativeKidsRequest.output B) (nativePrice : NativeStagePrice B) where
  span : ℕ
  program : WMX (span+29) 32
  capacity : TermCutRequest→ℕ
  cost : TermCutRequest→ℕ→ℕ
  run : ∀ (r : TermCutRequest) (k : ℕ) (hk : k<r.terms.length) (cap : ℕ),
    capacity r ≤ cap →
      ∃τ,WXExec cap program
        (((r.progressData k).state span r).setv 17
          (r.terms.length-(k+1))) τ (cost r k) ∧
        SimW ((r.progressData (k+1)).state span r) τ
  price : ∃ C E : ℕ,1 ≤ C ∧ 1 ≤ E ∧ ∀ (r : TermCutRequest) (mc : ℕ),
    1 ≤ mc → (∀i,(r.toRowContext.nativeKids i).length ≤ mc) →
      ∀ (k : ℕ) (hk : k<r.terms.length),
        cost r k ≤ C*(r.censusMagnitude mc)^E*mc^(2*r.terms[k].1.card)

end NearQuarticWires.StageTuple
