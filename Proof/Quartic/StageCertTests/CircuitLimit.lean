import Proof.Quartic.StageCertTests.SignSchedule

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertTests

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

/-- `sec:algorithm`, paper/paper.tex:
pair calls require both circuit blocks and other calls require the first. -/
def callCircuitCount : CallKind → ℕ
  | .single => 1 | .pair => 2 | .parity => 1

/-- `sec:algorithm`, paper/paper.tex:
the outer circuit bound and original call-kind tag are retained separately. -/
def circuitLimitVar : Fin VV := ⟨86,by decide⟩
def scheduleCallKindVar : Fin VV := ⟨87,by decide⟩

/-- `sec:algorithm`, paper/paper.tex:
the literal call-kind tag controls the actual number of circuit blocks. -/
def setCircuitLimit : St VV MM :=
  .ite (.eq scheduleCallKindVar v1) (setK circuitLimitVar 2) (setK circuitLimitVar 1)

/-- `sec:algorithm`, paper/paper.tex:
the physical branch reads the original kind tag and constructs
the exact active circuit count without a supplied circuit-set oracle. -/
theorem setCircuitLimit_spec (C : Ctx) (a : DS VV MM) (kind : CallKind) (hc : Cst a)
    (hk : a.env scheduleCallKindVar = kindTag kind) (hroom : 2 < 2^C.Wd) :
    Hs C setCircuitLimit a 8 (fun b =>
      b.env circuitLimitVar = callCircuitCount kind ∧ b.sh = a.sh ∧ Cst b ∧
      Fr a b [circuitLimitVar,vJ]) := by
  unfold setCircuitLimit
  have hpost (value : ℕ) (hv : value < 2^C.Wd) :
      Hs C (setK circuitLimitVar value) a (2*value+3) (fun b =>
        b.env circuitLimitVar = value ∧ b.sh = a.sh ∧ Cst b ∧ Fr a b [circuitLimitVar,vJ]) := by
    refine (setK_spec circuitLimitVar (by decide) value a hv).mono le_rfl ?_
    rintro b ⟨hbv,hbsh,hbfr⟩
    exact ⟨hbv,hbsh,Cst.of_fr hc hbfr (by decide),hbfr⟩
  cases kind
  · have he : (Cnd.eq scheduleCallKindVar v1).eval a = false := by simp [Cnd.eval,hk,hc.one,kindTag]
    exact (Hs.iteF (c := .eq scheduleCallKindVar v1) (show scheduleCallKindVar ≠ v1 by decide) he (hpost 1 (by omega))).mono
      (by omega) (fun _ h => h)
  · have he : (Cnd.eq scheduleCallKindVar v1).eval a = true := by simp [Cnd.eval,hk,hc.one,kindTag]
    exact (Hs.iteT (c := .eq scheduleCallKindVar v1) (show scheduleCallKindVar ≠ v1 by decide) he (hpost 2 hroom)).mono
      (by omega) (fun _ h => h)
  · have he : (Cnd.eq scheduleCallKindVar v1).eval a = false := by simp [Cnd.eval,hk,hc.one,kindTag]
    exact (Hs.iteF (c := .eq scheduleCallKindVar v1) (show scheduleCallKindVar ≠ v1 by decide) he (hpost 1 (by omega))).mono
      (by omega) (fun _ h => h)

/-- `sec:algorithm`, paper/paper.tex:
the exact selected circuit count fits the fixed two-circuit index type. -/
theorem callCircuitCount_bounds (kind : CallKind) : 1 ≤ callCircuitCount kind ∧ callCircuitCount kind ≤ 2 := by
  cases kind <;> decide

end NearQuarticWires.StageCertTests
