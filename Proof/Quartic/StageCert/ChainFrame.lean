import Proof.Quartic.StageCert.ChainRead
import Proof.Quartic.StageLift.StoreFrame
import Proof.Gates.Cells.Inv

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: coefficient-source
instructions do not emit formula tokens while reading retained bits. -/
private def sourceSilentOp {V M : ℕ} : Op V M → Prop
  | .emit _ => False
  | _ => True

/-- `lem:print`, paper/paper.tex: both source branches
and all actual prefix-scan iterations leave the token output untouched. -/
private def sourceSilent {V M : ℕ} : St V M → Prop
  | .op o => sourceSilentOp o
  | .seq s t | .ite _ s t => sourceSilent s ∧ sourceSilent t
  | .loop _ s => sourceSilent s

private theorem sourceSilentOp_spec {V M : ℕ} {C : Ctx} {o : Op V M}
    {a b : DS V M} {n : ℕ} (he : OpEx C o a b n) (h : sourceSilentOp o) :
    b.out=a.out := by
  cases he <;> simp_all [sourceSilentOp,DS.set,DS.adv,DS.put,DS.rew,DS.srt,DS.called]

private theorem sourceSilent_spec {V M : ℕ} {C : Ctx} {s : St V M}
    {a b : DS V M} {n : ℕ} (he : Ex C s a b n) (h : sourceSilent s) :
    b.out=a.out := by
  induction he with
  | op he => exact sourceSilentOp_spec he h
  | seq _ _ ih₁ ih₂ => exact (ih₂ h.2).trans (ih₁ h.1)
  | iteT _ _ _ ih => exact ih h.1
  | iteF _ _ _ ih => exact ih h.2
  | loopF => rfl
  | loopT _ _ _ _ ih₁ ih₂ => exact (ih₂ h).trans (ih₁ h)
  | mono _ _ ih => exact ih h

/-- (W3) and `lem:print`, paper/paper.tex: reading an actual proposed-chain bit cannot append tokens. -/
theorem readChainRecord_output {C : Ctx} (store : Fin MM) (target : Fin VV)
    {a b : DS VV MM} {n : ℕ} (he : Ex C (readChainRecord store target) a b n) :
    b.out=a.out := by
  apply sourceSilent_spec he
  simp [readChainRecord,prepareChainAddress,readSourceRecord,seekSourceRecord,
    forS,sourceSilent,sourceSilentOp]

/-- (W3) and `lem:print`, paper/paper.tex: the chain reader preserves every separately retained rate,
parameter or token store, including its physical cursor. -/
theorem readChainRecord_otherStore {C : Ctx} (store other : Fin MM)
    (hne : other≠store) (target : Fin VV) {a b : DS VV MM} {n : ℕ}
    (he : Ex C (readChainRecord store target) a b n) :
    b.ram other=a.ram other ∧ b.rc other=a.rc other := by
  apply StageLift.avoidsStore_spec he
  simp [readChainRecord,prepareChainAddress,readSourceRecord,seekSourceRecord,
    forS,StageLift.avoidsStore,StageLift.avoidsStoreOp,hne]

end NearQuarticWires.StageCert.Tokens
