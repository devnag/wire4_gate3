import Proof.Quartic.StageLift.CallKindSource
import Proof.Quartic.StageLift.TargetToken
import Proof.Quartic.StageLift.FermatToken
import Proof.Quartic.StageLift.AmplifierCoefficient
import Proof.Quartic.StageLift.RawHeader
import Proof.Quartic.StageCert.SourceFormulaDock

set_option autoImplicit false

namespace NearQuarticWires.StageLift
open NearCubicWires NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Tabulator
open NearCubicGates.Close.Interfaces.Formats

/-- `lem:residue` and `lem:print`, paper/paper.tex: the amplified actual normalized residue source. -/
noncomputable def residueBodyFormula {B1 B2 : ℕ}
    (r : Greedy.PrintRequest B1 B2) : Formula (17 * (Builder.allGates r.child.call).length) :=
  Formula.amp r.child.selected.1.e
    (StageLift.indexedFermatFormula r.prime
      (StageLift.callResidueForm r.child.call (Cells.prepare_spec _ r.child.selected.1 r.child.selected.2) r.child.witness r.pattern)
      (StageLift.callResidueTarget r.child.call r.child.selected.1 r.prime
        (fun j i => r.digits j i % (r.prime ^ r.child.selected.1.e : ℤ))
        (fun j => r.residues j % (r.prime ^ r.child.selected.1.e : ℤ))))

/-- `lem:print`, paper/paper.tex: explicit retained-source and binary-width invariants at the residue-body entry. -/
structure ResidueReady {B1 B2 : ℕ} (C : Ctx)
    (r : Greedy.PrintRequest B1 B2) (a : DS VV MM) (E : ℕ) : Prop where
  constants : Cst a
  valid : Valid C a
  parameterRecords : a.ram StageLift.parameterStore = StageLift.parameterScalars r.child.selected.1
  factorRecords : a.ram StageLift.factorStore = r.child.selected.1.factors
  witnessRecords : a.ram StageLift.witnessStore =
    (Program.witnessPrefix r.child.call r.child.selected.1 r.child.witness).map Bool.toNat
  indexRecords : a.ram StageLift.indexStore = StageLift.normalizedPrintIndex r
  exponent : a.env StageLift.degreeExponent = r.child.selected.1.e
  chainCount : a.env StageLift.degreeChain = r.child.selected.1.J
  modulus : a.env StageRecovery.modulusVar = r.prime ^ r.child.selected.1.e
  prime : a.env StageLift.degreePrime = r.prime
  signs : a.env StageLift.signCodeVar = StageLift.printPatternCode r.pattern
  kind : a.env StageLift.callKindVar = kindTag r.child.call.kind
  occurrences : a.env StageCert.Tokens.atomCount = (Builder.allGates r.child.call).length
  firstOccurrences : a.env StageCert.Tokens.firstGateCount = r.child.call.first.gates.length
  envelope_pos : 2 ≤ E
  occurrences_bound : (Builder.allGates r.child.call).length ≤ E
  exponent_bound : r.child.selected.1.e ≤ E
  chains_bound : r.child.selected.1.J ≤ E
  partition_bound : r.child.selected.1.k ≤ E
  prime_bound : r.prime ≤ E
  M1_bound : r.child.selected.1.M1 ≤ 2 ^ E
  A_bound : r.child.selected.1.A ≤ 2 ^ E
  factors_bound : ∀ v ∈ r.child.selected.1.factors, v ≤ 2 ^ E
  witness_length : (Program.witnessPrefix r.child.call r.child.selected.1 r.child.witness).length ≤ (E + 1) ^ 3
  width : 100 * (E + 1) ^ 2 ≤ C.Wd

/-- `lem:print`, paper/paper.tex: exact operational specification of the physically generated amplified residue source. -/
def residueBodyProgramSpec (body : St VV MM) : Prop :=
  ∀ {B1 B2 : ℕ} (C : Ctx)
    (r : Greedy.PrintRequest B1 B2) (a : DS VV MM) (E : ℕ)
    (_ready : ResidueReady C r a E),
    Hs C body a (10 ^ 12 * (E + 1) ^ 30) (fun b =>
      b.out = a.out ++ (toks (residueBodyFormula r)).flatMap tokWord ∧
      b.ram = a.ram ∧
      (∀ store, store ∉ [StageLift.parameterStore, StageLift.factorStore,
        StageLift.witnessStore, StageLift.indexStore] → b.rc store = a.rc store) ∧
      (b.ip, b.kin, b.kout, b.kc) = (a.ip, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Valid C b ∧
      (∀ x ∈ ([54, 55, 56, 57, 58, 59, 60, 63, 71, 72, 96, 127] : List (Fin VV)),
        b.env x = a.env x))
end NearQuarticWires.StageLift
