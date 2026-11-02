import Proof.Quartic.StageLift.PrintRequest
import Proof.Quartic.StageLift.PreparedCache

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: the actual
destination fields of each instruction determine its retained registers. -/
def avoidsRegisterOp {V M : ℕ} (x : Fin V) : Op V M → Prop
  | .zero y | .inc y | .add y _ | .sub y _ | .copy y _ | .half y | .shl y => x ≠ y
  | .rdI y | .rdM _ y | .rdK y => x ≠ y
  | .mul _ _ y => x ≠ y
  | .dm _ _ q r => x ≠ q ∧ x ≠ r
  | _ => True

/-- `lem:print`, paper/paper.tex: every branch
and actual iteration preserves a register absent from all destinations. -/
def avoidsRegister {V M : ℕ} (x : Fin V) : St V M → Prop
  | .op o => avoidsRegisterOp x o
  | .seq left right | .ite _ left right => avoidsRegister x left ∧ avoidsRegister x right
  | .loop _ body => avoidsRegister x body

instance avoidsRegisterOpDecidable {V M : ℕ} (x : Fin V) (o : Op V M) :
    Decidable (avoidsRegisterOp x o) := by
  cases o <;> dsimp only [avoidsRegisterOp] <;> infer_instance

instance avoidsRegisterDecidable {V M : ℕ} (x : Fin V) (s : St V M) :
    Decidable (avoidsRegister x s) :=
  match s with
  | .op _ => avoidsRegisterOpDecidable _ _
  | .seq left right | .ite _ left right =>
      @instDecidableAnd _ _ (avoidsRegisterDecidable x left) (avoidsRegisterDecidable x right)
  | .loop _ body => avoidsRegisterDecidable x body

/-- `lem:print`, paper/paper.tex: one real
instruction preserves each register outside its declared destinations. -/
theorem avoidsRegisterOp_spec {V M : ℕ} {C : Ctx} {x : Fin V}
    {o : Op V M} {a b : DS V M} {n : ℕ} (he : OpEx C o a b n)
    (ha : avoidsRegisterOp x o) : b.env x = a.env x := by
  cases he <;> simp_all [avoidsRegisterOp, DS.set, DS.adv, DS.put, DS.rew, DS.srt, DS.called]

/-- `lem:print`, paper/paper.tex: actual complete
executions preserve their syntactically untouched source metadata,
including through all runtime loop iterations and callee returns. -/
theorem avoidsRegister_spec {V M : ℕ} {C : Ctx} {x : Fin V}
    {s : St V M} {a b : DS V M} {n : ℕ} (he : Ex C s a b n)
    (ha : avoidsRegister x s) : b.env x = a.env x := by
  induction he with
  | op h => exact avoidsRegisterOp_spec h ha
  | seq _ _ ih₁ ih₂ => exact (ih₂ ha.2).trans (ih₁ ha.1)
  | iteT _ _ _ ih => exact ih ha.1
  | iteF _ _ _ ih => exact ih ha.2
  | loopF => rfl
  | loopT _ _ _ _ ih₁ ih₂ => exact (ih₂ ha).trans (ih₁ ha)
  | mono _ _ ih => exact ih ha

/-- Step 3 and `lem:print`, paper/paper.tex: the measured small preparation-word length survives
the complete actual original-source and unbounded-index parser. -/
theorem readPrintRequest_preserves_preparedLength {C : Ctx} {a b : DS VV MM} {n : ℕ}
    (he : Ex C readPrintRequest a b n) : b.env preparedLength = a.env preparedLength :=
  avoidsRegister_spec he (by decide)

end NearQuarticWires.StageLift
