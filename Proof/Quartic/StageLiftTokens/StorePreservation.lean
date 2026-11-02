import Proof.Quartic.StageCert.DigitWalkForm
import Proof.Quartic.StageLift.RegisterFrame

/-!
# Source stores outside the digit scans

`lem:print`, paper/paper.tex: the digit-form
instruction tree reads only the retained witness and factor stores;
all other source-store cursors remain unchanged on every execution.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftTokens
open NearCubicGates.Close.Cells StageLift StageCert.Tokens

instance storeOpDecidable {V M : ℕ} (store : Fin M) (o : Op V M) :
    Decidable (avoidsStoreOp store o) := by
  cases o <;> dsimp only [avoidsStoreOp] <;> infer_instance

instance storeDecidable {V M : ℕ} (store : Fin M) (s : St V M) :
    Decidable (avoidsStore store s) :=
  match s with
  | .op _ => storeOpDecidable _ _
  | .seq left right | .ite _ left right =>
      @instDecidableAnd _ _ (storeDecidable store left) (storeDecidable store right)
  | .loop _ body => storeDecidable store body

theorem digitForm_avoids :
    ∀store : Fin MM,store∉[witnessStore,factorStore]→
      avoidsStore store (emitDigitWalkForm witnessStore factorStore) := by decide

theorem digitForm_other_cursors {C : Ctx} {a b : DS VV MM} {n : ℕ}
    (he : Ex C (emitDigitWalkForm witnessStore factorStore) a b n)
    (store : Fin MM) (hs : store∉[witnessStore,factorStore]) : b.rc store=a.rc store :=
  (avoidsStore_spec he (digitForm_avoids store hs)).2

end NearQuarticWires.StageLiftTokens
