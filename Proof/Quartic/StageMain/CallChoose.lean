import Proof.Quartic.StageMain.CallHeader
import Proof.Quartic.StageMain.TableBit
import Proof.Gates.Interfaces.Counter

/-!
# Selecting the single, pair, or parity predicate

Paper: `def:class`, paper/paper.tex, and Step 4 of
`sec:algorithm`. The call kind selects the first circuit
value, the exclusive-or of the two circuit values, or the exclusive-or
of the first circuit value with the indexed input parity.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces

def xorTable (x y : Fin VV) : St VV := .ite (.eq x y)
  (.op (.zero tableResult)) (.op (.copy tableResult v1))

theorem xorTable_spec {C : Ctx} (x y : Fin VV) (hxy : x ≠ y) (a : DS VV) (hc : Cst a)
    (v w : Bool) (hv : a.env x = v.toNat) (hw : a.env y = w.toNat) :
    Hs C (xorTable x y) a 2 (fun b => b.env tableResult = (xor v w).toNat ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b [tableResult]) := by
  cases v <;> cases w
  all_goals
    first
    | have he : (Cnd.eq x y).eval a = true := by simp [Cnd.eval, hv, hw]
      refine Hs.mono (Hs.iteT hxy he (hs_zero C tableResult a)) le_rfl ?_
      rintro b rfl
      exact ⟨by simp, rfl, rfl, rfl, hc.set _ _ (by decide), Fr.set _ _ (by decide)⟩
    | have he : (Cnd.eq x y).eval a = false := by simp [Cnd.eval, hv, hw]
      refine Hs.mono (Hs.iteF hxy he (hs_copy C tableResult v1 a (by decide))) le_rfl ?_
      rintro b rfl
      exact ⟨by simp [hc.one], rfl, rfl, rfl, hc.set _ _ (by decide), Fr.set _ _ (by decide)⟩

def callChoice (kind : CallKind) (v w p : Bool) : Bool :=
  match kind with
  | .single => v
  | .pair => xor v w
  | .parity => xor v p

def callChoose : St VV := .ite (.eq callKind vZ) (.op (.copy tableResult firstValue))
  (.ite (.eq callKind v1) (xorTable firstValue secondValue) (xorTable firstValue parityResult))

theorem callChoose_spec {C : Ctx} (a : DS VV) (hc : Cst a) (kind : CallKind) (v w p : Bool)
    (hk : a.env callKind = kindTag kind) (hv : a.env firstValue = v.toNat)
    (hw : a.env secondValue = w.toNat) (hp : a.env parityResult = p.toNat) :
    Hs C callChoose a 4 (fun b => b.env tableResult = (callChoice kind v w p).toNat ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b [tableResult]) := by
  cases kind with
  | single =>
    have he : (Cnd.eq callKind vZ).eval a = true := by simp [Cnd.eval, hk, kindTag, hc.z]
    refine Hs.mono (Hs.iteT (show callKind ≠ vZ by decide) he
      (hs_copy C tableResult firstValue a (by decide))) (by omega) ?_
    rintro b rfl
    exact ⟨by simp [callChoice, hv], rfl, rfl, rfl, hc.set _ _ (by decide), Fr.set _ _ (by decide)⟩
  | pair =>
    have h0 : (Cnd.eq callKind vZ).eval a = false := by simp [Cnd.eval, hk, kindTag, hc.z]
    have h1 : (Cnd.eq callKind v1).eval a = true := by simp [Cnd.eval, hk, kindTag, hc.one]
    exact Hs.iteF (show callKind ≠ vZ by decide) h0
      (Hs.iteT (show callKind ≠ v1 by decide) h1
        (xorTable_spec firstValue secondValue (by decide) a hc v w hv hw))
  | parity =>
    have h0 : (Cnd.eq callKind vZ).eval a = false := by simp [Cnd.eval, hk, kindTag, hc.z]
    have h1 : (Cnd.eq callKind v1).eval a = false := by simp [Cnd.eval, hk, kindTag, hc.one]
    exact Hs.iteF (show callKind ≠ vZ by decide) h0
      (Hs.iteF (show callKind ≠ v1 by decide) h1
        (xorTable_spec firstValue parityResult (by decide) a hc v p hv hp))

end NearQuarticWires.StageMain
