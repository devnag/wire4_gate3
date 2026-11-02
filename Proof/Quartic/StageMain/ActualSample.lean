import Proof.Quartic.StageMain.SampleCall
import Proof.Quartic.Cycle.ConditionalGamma

/-!
# The sampler kernel evaluates the actual seeded sample positions

`imp:seed`, paper/paper.tex, fixes the field polynomial and
its projection to a pair of cell indices. Step 4 of `sec:algorithm`, uses these positions for the chosen seed. The physical
kernel's binary result has precisely those projected coordinates.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5

noncomputable def actualSampleRequest (P : Sampler.SeedParams) (seed : ℕ) (j : Fin P.Q) :
    SampleRequest where
  ell := P.ell
  modulus := P.modulus
  seed := seed
  label := j.val
  positive := P.one_le_ell
  modulus_ok := P.cert.2.1
  label_lt := j.isLt.trans_le P.Q_le

theorem actualSampleOutput (P : Sampler.SeedParams) (seed : ℕ) (j : Fin P.Q) :
    sampleRawOutput (actualSampleRequest P seed j) =
      frame (binary P.ell (JoinElimination.gen P.modulus P.ell 8 seed j)) := rfl

theorem actualSamplePosition (P : Sampler.SeedParams) (seed : ℕ) (j : Fin P.Q) :
    Cycle.seedSample P seed j = P.cellEquiv
      (fun b => GF.bitF ((JoinElimination.gen P.modulus P.ell 8 seed j).testBit b)) :=
  Sampler.pos_eq_gen P seed j

theorem actualSampleValue_lt (P : Sampler.SeedParams) (seed : ℕ) (j : Fin P.Q) :
    JoinElimination.gen P.modulus P.ell 8 seed j < 2 ^ P.ell :=
  (Sampler.gen_spec P.modulus P.ell seed j P.cert.2.1 P.one_le_ell
    (j.isLt.trans_le P.Q_le) 8).1

end NearQuarticWires.StageMain
