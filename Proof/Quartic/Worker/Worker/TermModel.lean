import Proof.Quartic.Worker.Prelude
import Proof.Quartic.Worker.Worker.Operands
import Proof.Quartic.Worker.WorkerArith.SuppEqDefs
import Proof.Quartic.Worker.WorkerArith.Entries

/-!
# Worker.TermModel for the weak machine of the wire measure

* `Opd.atom`: The atom an operand names.
* `model1`: **The entry of a one-operand term.**.
* `model2`: **The entry of a two-operand term.**.

Adapted from `Proof.Gates.Worker.TermModel` of the near-cubic gate proof, with the wire measure and the cap 𝒜₄: the counter is `Counter4`
(`NearQuarticWires.Worker4.Counter`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Worker4.Worker
open NearCubicGates NearCubicGates.Close NearCubicGates.Close.Worker

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairOrdinary
open NearCubicWires.Bindings.CLW20Lemma311 NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Codec NearQuarticWires.Worker4.Codec
open NearQuarticWires.Worker4.WorkerArith (sysList halfIf)

/-- An operand in registers: flip, systematic?, index. -/
structure Opd where
  neg : Bool
  sys : Bool
  idx : ℕ

/-- The atom an operand names. -/
def Opd.atom (o : Opd) : Atom := if o.sys then .sys o.idx else .aux o.idx

section Model
variable {B1 B2 : ℕ} (ctr : Counter B1 B2) {q : ℕ} (Cs : ℕ → NCircuit q) (rows : ℕ → List ℕ) (ω : ℚ)
  (w : List Bool)

/-- **The entry of a one-operand term.** -/
noncomputable def model1 (o : Opd) : Bool × (ℚ × ℚ) :=
  if o.sys then (o.neg, (halfIf (decide (sysList q rows o.idx ≠ [])), 0))
  else (o.neg, ctr.value (oneCallOf Cs o.idx [] ω) w)

/-- **The entry of a two-operand term.** -/
noncomputable def model2 (o1 o2 : Opd) : Bool × (ℚ × ℚ) :=
  match o1.sys, o2.sys with
  | true, true => (xor o1.neg o2.neg, (halfIf (decide (sysList q rows o1.idx ≠ sysList q rows o2.idx)), 0))
  | true, false => (xor o1.neg o2.neg, ctr.value (oneCallOf Cs o2.idx (sysList q rows o1.idx) ω) w)
  | false, true => (xor o1.neg o2.neg, ctr.value (oneCallOf Cs o1.idx (sysList q rows o2.idx) ω) w)
  | false, false =>
    (xor o1.neg o2.neg, if o1.idx = o2.idx then (0, 0) else ctr.value (pairCallOf Cs o1.idx o2.idx ω) w)

end Model

end NearQuarticWires.Worker4.Worker
