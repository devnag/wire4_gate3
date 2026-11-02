import Proof.Quartic.StageMain.SampleTaggedData
import Proof.Quartic.StageMain.SampleStep

/-!
# Executing the sampler through the tagged main-pass interface

`imp:seed`, paper/paper.tex, and Step 4 of
`sec:algorithm`: the controller emits the selector bit
and all sampler records before the actual ordinary call. The shared
call reservation is charged on every execution.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.SampleCells

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open StageGamma

variable {Req : Type} {rightInput rightOutput : Req → List Bool} {rightBudget : Req → ℕ}

noncomputable def taggedContext (width : ℕ) (input : List Bool)
    (f : WordFunction Req rightInput (fun r => frame (rightOutput r)) rightBudget)
    (L B : ℕ) : Ctx := ⟨width, input, sampleTaggedCallee f, L, B⟩

def taggedSampleCall : St VV MM :=
  .seq (.op (.kem false)) (.seq sampleRecipe.program (.op .kcall))

theorem taggedSampleCall_run
    (f : WordFunction Req rightInput (fun r => frame (rightOutput r)) rightBudget)
    (r : SampleRequest) (width : ℕ) (input : List Bool) (L B : ℕ)
    (a : DS VV MM) (hc : Cst a) (ha : SampleStored r a)
    (hkin : a.kin = []) (hwidth : r.ell + 2 ≤ width)
    (hL : 10000 * (r.ell + 1) + 1 ≤ L)
    (hB : 30000000 * (r.ell + 1) ^ 2 ≤ B) :
    Hs (taggedContext width input f L B) taggedSampleCall a (2 * L + B + 10) (fun b =>
      b.kout = sampleRawOutput r ∧ b.kc = 0 ∧ b.kin = [] ∧
      b.ip = a.ip ∧ b.out = a.out ∧ b.ram = a.ram ∧ b.rc = a.rc ∧
      Cst b ∧ Fr a b writerScratch) := by
  let C := taggedContext width input f L B
  refine Hs.mono (Hs.seq (t1 := 1) (t2 := sampleRecipe.cost a + (1 + L + B) + 1)
    (hs_kem C false a (by simp [C, taggedContext, hkin]; omega)) ?_) ?_ (fun _ h => h)
  · rintro b rfl
    let a1 : DS VV MM := { a with kin := a.kin ++ [false] }
    have hc1 : Cst a1 := ⟨hc.z, hc.one, hc.two⟩
    have ha1 : SampleStored r a1 := ⟨ha.degree, ha.field, ha.sampleLabel, ha.coeff⟩
    have hcost := sampleRecipe_cost r a1 ha1
    have hw := sampleRecipe_run r C a1 hc1 ha1 (by dsimp [C, taggedContext]; omega)
      (sampleRecipe_params_fit r a1 hc1 ha1 width hwidth)
      (by
        change a1.kin.length + sampleRecipe.cost a1 ≤ L
        have hlen : a1.kin.length = 1 := by simp [a1, hkin]
        rw [hlen]
        omega)
    refine Hs.seq (t1 := sampleRecipe.cost a) (t2 := 1 + L + B) hw ?_
    intro b ⟨hb, hs, hbc, hfr⟩
    have hin : b.kin = C.K.inw (.inl r) := by
      simpa [C, taggedContext, sampleTaggedCallee, Tagged.taggedInput, a1, hkin] using hb
    have he : Hs C (.op .kcall) b (1 + L + B)
        (fun d => d = b.called (sampleRawOutput r)) :=
      Hs.op (OpEx.kcall (C := C) (.inl r) b hin ((sampleTaggedCallee_budget f r).trans hB)) rfl
    refine he.mono le_rfl ?_
    rintro d rfl
    exact ⟨rfl, rfl, rfl, hs.ip, hs.out, hs.ram, hs.rc,
      ⟨hbc.z, hbc.one, hbc.two⟩, hfr⟩
  · have hcost := sampleRecipe_cost r a ha
    omega

end NearQuarticWires.StageMain.SampleCells
