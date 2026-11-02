import Proof.Quartic.StageRecovery.TermsSyntaxCost
import Proof.Quartic.StageLift.TupleResidue

set_option autoImplicit false

namespace NearQuarticWires.StageRecovery

open NearCubicWires
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats

/-- `lem:print`, paper/paper.tex: the actual literal
Formula compiler request chooses its squared structural hint from its
own complete serialized Formula, with no supplied workspace oracle. -/
def literalCompileRequest {V : ℕ} (F : Formula V) (q : ℕ) (hq : 2 ≤ q)
    (D : ℕ) (hD : F.degree ≤ D) : FamilyCompileRequest where
  source := {
    arity := V
    formula := F
    modulus := q
    hint := (V + F.size + (formulaWord ⟨V, F⟩).length + natBitLength q + 10) ^ 2
    modulus_ge_two := hq
    hint_sufficient := le_rfl }
  degree := D
  degree_bound := hD

/-- `lem:print`, paper/paper.tex: the chosen
workspace header is exactly the squared actual syntax magnitude. -/
theorem literalCompileRequest_hint {V : ℕ} (F : Formula V) (q : ℕ) (hq : 2 ≤ q)
    (D : ℕ) (hD : F.degree ≤ D) :
    (literalCompileRequest F q hq D hD).source.hint =
      (literalCompileRequest F q hq D hD).source.syntaxMagnitude ^ 2 := rfl

/-- `lem:residue` and `lem:print`, paper/paper.tex: the concrete selected per-walk compiler input uses the
actual normalized tuple-mask/Fermat/amplifier Formula on the shared atom pool. -/
noncomputable def residueCompileRequest (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (walk : Cycle.Walk hs.seedParameters.N 4) (sigma : Cycle.SignPattern 4)
    (prime : ℕ) (hprime : prime ∈ p.primes)
    (digits : Fin 2 → Fin (p.J - 1 + 1) → ℤ) (residues : Fin 2 → ℤ) (weight : ℤ) :
    FamilyCompileRequest :=
  literalCompileRequest
    (StageLift.reduceConstants (prime ^ p.e)
      (StageLift.tupleResidueWalkFormula c hs w walk sigma prime digits residues weight))
    (prime ^ p.e) (StageLift.selected_modulus_ge_two hs prime hprime)
    (StageLift.residueDegreeBound p prime) (by
      rw [StageLift.reduceConstants_degree]
      exact StageLift.tupleResidueWalkFormula_degree c hs w walk sigma prime digits residues weight)

/-- `prop:time`, paper/paper.tex: the
explicit polynomial multiplier for the actual normalized residue syntax
includes both codec headers and the selected degree/modulus fields. -/
def residueCompilerFactor (G X J prime e D : ℕ) : ℕ :=
  6 * ((StageLift.formulaByteFactor (17 * G) (prime ^ e) + 1) *
    StageLift.residueSyntaxPolynomial G X J prime e) +
      3 * (17 * G) + D + natBitLength (prime ^ e) + 20

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual concrete normalized per-walk Formula obeys
the syntax envelope used by the physical compiler's proved cost. -/
theorem residueCompileRequest_syntax (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (walk : Cycle.Walk hs.seedParameters.N 4) (sigma : Cycle.SignPattern 4)
    (prime : ℕ) (hprime : prime ∈ p.primes)
    (digits : Fin 2 → Fin (p.J - 1 + 1) → ℤ) (residues : Fin 2 → ℤ) (weight : ℤ) :
    let r := residueCompileRequest c hs w walk sigma prime hprime digits residues weight
    r.syntaxMagnitude ≤
      residueCompilerFactor (Builder.allGates c).length p.Xmax (p.J - 1) prime p.e r.degree *
        (r.source.arity + 1) ^ (p.Xmax + 1) := by
  dsimp only
  let r := residueCompileRequest c hs w walk sigma prime hprime digits residues weight
  let B := 2 * (StageLift.formulaByteFactor (17 * (Builder.allGates c).length) (prime ^ p.e) + 1) *
    StageLift.residueSyntaxPolynomial (Builder.allGates c).length p.Xmax (p.J - 1) prime p.e
  have hq : 0 < prime ^ p.e := by
    have h := StageLift.selected_modulus_ge_two hs prime hprime
    omega
  have hb := StageLift.reduced_tuple_residue_size_bytes_bound c hs w walk sigma prime hq digits residues weight
  have hbytes : r.source.formula.size + (tokenStream (toks r.source.formula)).length ≤
      B * (r.source.arity + 1) ^ (p.Xmax + 1) := by
    simpa only [r, residueCompileRequest, literalCompileRequest, StageLift.reduceConstants_size,
      StageLift.formulaTokenBytes, tokenStream, B] using hb
  convert r.syntaxMagnitude_le B p.Xmax hbytes using 1
  dsimp [residueCompilerFactor, B, r, residueCompileRequest, literalCompileRequest]
  ring

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual normalized residue request inherits the
complete physical compiler cost with the exact source exponent. -/
theorem residueCompileRequest_budget (c : Call) {p : Cells.Parameters}
    (hs : Cells.ParameterRules (Builder.callInput c) p) (w : List Bool)
    (walk : Cycle.Walk hs.seedParameters.N 4) (sigma : Cycle.SignPattern 4)
    (prime : ℕ) (hprime : prime ∈ p.primes)
    (digits : Fin 2 → Fin (p.J - 1 + 1) → ℤ) (residues : Fin 2 → ℤ) (weight : ℤ) :
    let r := residueCompileRequest c hs w walk sigma prime hprime digits residues weight
    r.modularTermsBudget ≤ 4 * 27 * 10 ^ 22 * (TSK packetCallee + 10) *
      (residueCompilerFactor (Builder.allGates c).length p.Xmax (p.J - 1) prime p.e r.degree) ^ 6 *
        (r.source.arity + 1) ^ (2 * r.degree + 6 * p.Xmax + 6) := by
  dsimp only
  exact (residueCompileRequest c hs w walk sigma prime hprime digits residues weight).modularTermsBudget_exponent_le
    _ p.Xmax rfl (residueCompileRequest_syntax c hs w walk sigma prime hprime digits residues weight)

end NearQuarticWires.StageRecovery
