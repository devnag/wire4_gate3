import Proof.Quartic.StageCert.SourceMomentDock
import Proof.Quartic.StageCert.SourceCallGuards
import Proof.Quartic.StageCert.PopulationMoment
import Proof.Quartic.StageFormulaMetadata.Packet

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Tabulator

/-- `eq:testX`–`eq:testPhi` and `lem:print`, paper/paper.tex: population sums over N² cells; digit and
final-error moments sum over N⁸ original fixed m=4 walks. -/
def momentTermCount {J : ℕ} (N : ℕ) : StageCertTests.TestOrdinal J→ℕ
  | .population => N^2
  | .digit _ _ _ | .finalError _ _ => N^8

/-- `sec:algorithm` and `lem:print`, paper/paper.tex: one cold moment-source request has only the original
call, selected public parameters, witness, whole-test ordinal and actual
term ordinal. It contains no Formula, mask, incidence data or token count. -/
structure MomentRequest (B1 B2 : ℕ) where
  call : Call
  selected : Program.Selected call
  dispatched : Program.dispatch B1 B2 call=some selected
  witness : List Bool
  test : StageCertTests.TestOrdinal (selected.1.J-1)
  index : Fin (momentTermCount selected.1.N test)

/-- `sec:params`, paper/paper.tex: the actual
selected call supplies precisely the public rules used by its source. -/
theorem MomentRequest.rules {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    Cells.ParameterRules (Builder.callInput r.call) r.selected.1 :=
  Cells.prepare_spec _ r.selected.1 r.selected.2

/-- (W1)–(W3), `sec:algorithm`, paper/paper.tex: only the actual
finite zero-padded witness prefix is retained by the cold source. -/
def MomentRequest.retainedWitness {B1 B2 : ℕ} (r : MomentRequest B1 B2) : List Bool :=
  Program.witnessPrefix r.call r.selected.1 r.witness

/-- `sec:algorithm` and `lem:print`, paper/paper.tex: the sole source bytes are the literal prep word,
the five natural test fields and the actual low-first term ordinal. -/
noncomputable def MomentRequest.word {B1 B2 : ℕ} (r : MomentRequest B1 B2) : List Bool :=
  Program.prepWord B1 B2 r.call r.witness++(r.test.metadata r.selected.1).word++natWord r.index.val

/-- `sec:cycle` and `lem:print`, paper/paper.tex: all eight pattern indices are computed from the same
actual low-first radix-N source ordinal. Population ordinals below N²
have zero remaining digits and therefore enumerate each cell once. -/
def MomentRequest.walk {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    Cycle.Walk r.rules.seedParameters.N 4 := fun l=>
  ⟨r.index.val/r.selected.1.N^l.val%r.selected.1.N,by
    rw [Cells.ParameterRules.seed_N r.rules]
    exact Nat.mod_lt _ (lt_of_lt_of_le (by decide : 0<2) (Cells.ParameterRules.N_ge_two r.rules))⟩

/-- `lem:print`, paper/paper.tex: the exact
integer per-term Formula on the original seventeen-role occurrence pool. -/
noncomputable def MomentRequest.formula {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    Formula (17*(Builder.allGates r.call).length) :=
  match r.test with
  | .population => StagePrint.selectedPopulationMomentFormula (by decide : 0<4)
      (fun i=>r.retainedWitness.getD (r.selected.1.k+i.val) false) 0
      (StagePrint.callStructural r.call r.rules r.walk 0) r.selected.1.k
  | .digit j code row => sourceDigitMomentFormula (Builder.allGates r.call).length row.val
      r.selected.1.J r.selected.1.k j.val r.call.first.gates.length code.val
      r.selected.1.tau r.selected.1.Xmax r.retainedWitness r.selected.1.factors
      (StagePrint.callStructural r.call r.rules r.walk)
  | .finalError j code => sourceFinalMomentFormula (Builder.allGates r.call).length
      r.selected.1.J r.selected.1.k r.selected.1.M1 r.selected.1.A j.val r.call.first.gates.length
      code.val r.selected.1.tau r.selected.1.Xmax r.retainedWitness
      (StagePrint.callStructural r.call r.rules r.walk)

/-- `lem:print` and `prop:time`, paper/paper.tex: exact CERT uses the shared raw packet with q=0,
literal source degree and arity, and actual signed postfix payload. -/
noncomputable def MomentRequest.packet {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    StageFormulaMetadata.RawWalkPacket where
  index := r.index.val
  degree := 16*r.selected.1.Xmax+8*r.selected.1.k
  modulus := 0
  arity := 17*(Builder.allGates r.call).length
  payload := (toks r.formula).flatMap tokWord

/-- `lem:print`, paper/paper.tex: every actual
dispatched moment source has a nonempty original atom pool. -/
theorem MomentRequest.pool_pos {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    0<(Builder.allGates r.call).length := dispatched_originalPool_pos r.dispatched

/-- (W1)–(W3), `sec:algorithm`, paper/paper.tex: the actual
retained source meets the whole original proposed-chain horizon. -/
theorem MomentRequest.retainedWitness_length {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    r.retainedWitness.length=r.selected.1.k+(r.selected.1.J+1)*(Builder.allGates r.call).length :=
  source_witness_prefix_length r.call r.selected.1 r.witness

end NearQuarticWires.StageCert.Tokens
