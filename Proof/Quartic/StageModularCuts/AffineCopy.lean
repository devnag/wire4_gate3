import Proof.Quartic.StageModularCuts.CopyFields
import Proof.Wire_3_5.FinalPassHashTable

set_option autoImplicit false

namespace NearQuarticWires.StageModularCuts

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass.Hash4
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Recovery.HTParts

/-- `lem:print`, paper/paper.tex: the actual retained
affine-field count drives one byte-preserving field-copy pass. -/
def copyAffine : Program := .seq (.wm (wcopyR 8 9 12)) (.wm copyFields)

/-- `lem:print` and `prop:time`, paper/paper.tex: copying the fixed affine part restores its count registers
and adds only the literal outer-marked field bytes to the output. -/
theorem copyAffine_spec (cap : ℕ) (fields : List (List Bool))
    (pre suffix : List Bool) (a : State)
    (hsource : a.st 3 = pre ++ fields.flatMap frame ++ suffix)
    (hhead : a.sh 3 = pre.length) (hout : a.sh 14 = (a.st 14).length)
    (hstride : a.val 8 = fields.length) (hK : a.val 9 = 0) (hT : a.val 12 = 0)
    (hOP : a.val 6 + 2 * (fields.flatMap frame).length ≤ cap)
    (hsourceCap : a.val 5 + (fields.flatMap frame).length ≤ cap)
    (hcountCap : fields.length ≤ cap) :
    WXExec cap copyAffine a
      (adv 3 14 6 5 a (marks (fields.flatMap frame)) (fields.flatMap frame).length)
      (55 * (fields.flatMap frame).length + 22 * fields.length + 5) := by
  have e1 := wcopyR_spec cap (8 : Fin 16) 9 12
    (by decide) (by decide) (by decide) a hK hT (by rw [hstride]; exact hcountCap)
  rw [hstride] at e1
  let b := a.setv 9 fields.length
  have e2 := copyFields_spec cap fields pre suffix b hsource hhead hout
    (by simp [b])
    (by change Function.update a.val 9 fields.length 6 + _ ≤ cap
        rw [Function.update_of_ne (show (6 : Fin 16) ≠ 9 by decide)]
        exact hOP)
    (by change Function.update a.val 9 fields.length 5 + _ ≤ cap
        rw [Function.update_of_ne (show (5 : Fin 16) ≠ 9 by decide)]
        exact hsourceCap)
    hcountCap
  refine (WXExec.seq (WXExec.wm e1) (WXExec.wm e2)).cast cap ?_ (by omega)
  rw [show b = a.setv 9 fields.length from rfl,
    adv_setv _ _ _ (9 : Fin 16) _ (by decide) (by decide), wsetv_setv]
  have hz : (adv 3 14 6 5 a (marks (fields.flatMap frame)) (fields.flatMap frame).length).val 9 = 0 := by
    rw [adv_val_other _ _ _ (9 : Fin 16) (by decide) (by decide), hK]
  exact BinW.setv_same hz

end NearQuarticWires.StageModularCuts
