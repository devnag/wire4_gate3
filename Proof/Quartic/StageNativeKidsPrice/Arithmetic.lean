import Proof.Quartic.StageNativeKidsPrice.Polynomial

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKidsPrice

open Lean Meta Elab Tactic

private partial def closePrice (hp : TSyntax `term) (g : MVarId) : TacticM Unit :=
  g.withContext do
    let target := (← instantiateMVars (← g.getType)).consumeMData
    for decl in ← getLCtx do
      unless decl.isImplementationDetail do
        if ← withReducible (isDefEq target decl.type) then
          g.assign decl.toExpr
          return
    let args := target.getAppArgs
    unless target.isAppOfArity ``Price 3 do
      throwError "expected a structural polynomial price, received {target}"
    let charge := (← instantiateMVars args[2]!).consumeMData
    let .lam _ _ body _ := charge | throwError "expected a scalar charge function: {charge}"
    setGoals [g]
    if !body.hasLooseBVars then
      evalTactic (← `(tactic| exact Price.constant _ _))
    else
      let head := body.consumeMData.getAppFn.constName?
      if head == some ``HAdd.hAdd || head == some ``Nat.add then
        evalTactic (← `(tactic| apply Price.add $hp))
      else if head == some ``HMul.hMul || head == some ``Nat.mul then
        evalTactic (← `(tactic| apply Price.mul))
      else if head == some ``HPow.hPow || head == some ``Nat.pow then
        evalTactic (← `(tactic| apply Price.power))
      else
        throwError "no structural price supplied for scalar atom: {body}"
      let goals ← getGoals
      for subgoal in goals do closePrice hp subgoal
    setGoals []

elab "price_with " hp:term : tactic => do closePrice hp (← getMainGoal)

end NearQuarticWires.StageNativeKidsPrice
