import Proof.Quartic.StageLift.ResidueContract

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Tabulator
open NearCubicGates.Close.Interfaces.Formats

/-- `lem:print`, paper/paper.tex: the original
residue-source output and frame, unchanged by compact-prefix retention. -/
def residueBodyOutput {B1 B2 : ℕ} (C : Ctx) (r : Greedy.PrintRequest B1 B2)
    (a b : DS VV MM) : Prop :=

      b.out = a.out ++ (toks (residueBodyFormula r)).flatMap tokWord ∧
      b.ram = a.ram ∧
      (∀ store, store ∉ [StageLift.parameterStore, StageLift.factorStore,
        StageLift.witnessStore, StageLift.indexStore] → b.rc store = a.rc store) ∧
      (b.ip, b.kin, b.kout, b.kc) = (a.ip, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Valid C b ∧
      (∀ x ∈ ([54, 55, 56, 57, 58, 59, 60, 63, 71, 72, 96, 127] : List (Fin VV)),
        b.env x = a.env x)

/-- `lem:print`, paper/paper.tex: the existing
residue-source contract additionally preserves the actual compact-prefix
length throughout every original-source replay. -/
def residueBodyProgramWithCacheSpec (body : St VV MM) : Prop :=
  ∀ {B1 B2 : ℕ} (C : Ctx) (r : Greedy.PrintRequest B1 B2)
    (a : DS VV MM) (E : ℕ) (_ready : ResidueReady C r a E),
    Hs C body a (10 ^ 12 * (E + 1) ^ 30) (fun b =>
      residueBodyOutput C r a b ∧ b.env (76 : Fin VV) = a.env (76 : Fin VV))

/-- `lem:print`, paper/paper.tex: the added cache
frame strengthens the original source contract without altering it. -/
theorem residueBodyProgramWithCacheSpec_weakens {body : St VV MM}
    (h : residueBodyProgramWithCacheSpec body) : residueBodyProgramSpec body := by
  intro B1 B2 C r a E ready
  exact (h C r a E ready).mono le_rfl (fun _ hb => hb.1)

end NearQuarticWires.StageLift
