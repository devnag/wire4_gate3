import Proof.Gates.Interfaces.Counter
import Proof.Quartic.Machine.Counts

set_option autoImplicit false

namespace NearQuarticWires.Machine

open NearCubicWires.RepairOrdinary

/-- `thm:counter`, paper/paper.tex, and `prop:time`:
only the call codec and arity are needed by the machine obligations.  The
quartic admission predicate is supplied by the owner of `Counter4`. -/
structure CallEncoding (Call : Type) where
  arity : Call → ℕ
  word : Call → List Bool

/-- `sec:algorithm`, paper/paper.tex: a witness word is separate
from the normalized call; its unused suffix must not be scanned. -/
def requestWord {Call : Type} (encoding : CallEncoding Call)
    (request : Call × List Bool) : List Bool :=
  frame (encoding.word request.1) ++ frame request.2

/-- `prop:time`, paper/paper.tex: the realized interval is encoded
with the existing exact rational codec. -/
def intervalWord (interval : ℚ × ℚ) : List Bool :=
  NearCubicGates.Close.Interfaces.outputWord interval

/-- `prop:time`, paper/paper.tex: data alone do not constitute a
program or a time proof.  In particular no budget bound is a field here. -/
structure MachineSpecification (Call : Type) where
  value : Call → List Bool → ℚ × ℚ
  budget : Call → List Bool → ℕ

/-- `prop:time`, paper/paper.tex: the exact `Counter.program`
obligation, kept separate from the existence of any implementation. -/
def ProgramObligation {Call : Type} (encoding : CallEncoding Call)
    (specification : MachineSpecification Call) : Prop :=
  Nonempty (WordFunction (Call × List Bool) (requestWord encoding)
    (fun request => intervalWord (specification.value request.1 request.2))
    (fun request => specification.budget request.1 request.2))

/-- `prop:time`, paper/paper.tex: the integer-multiplied form of
`budget ≤ 2^n/n^mu`, exactly the existing `Counter.fast` convention. -/
def FastObligation {Call : Type} (encoding : CallEncoding Call)
    (admitted : Call → Prop) (mu : ℕ → ℕ)
    (specification : MachineSpecification Call) : Prop :=
  ∃ onset : ℕ, ∀ call : Call, onset ≤ encoding.arity call → admitted call →
    ∀ witness : List Bool,
      specification.budget call witness * encoding.arity call ^ mu (encoding.arity call) ≤
        2 ^ encoding.arity call

/-- `thm:counter`, paper/paper.tex, and `prop:time`:
malformed calls must be rejected without traversing an arbitrary witness. -/
def RestObligation {Call : Type} (encoding : CallEncoding Call)
    (admitted : Call → Prop) (specification : MachineSpecification Call) : Prop :=
  ∃ K exponent : ℕ, ∀ call witness, ¬ admitted call →
    specification.budget call witness ≤ K * ((encoding.word call).length + 1) ^ exponent

/-- `prop:time`, paper/paper.tex: a proved prefix-insensitivity
statement is required independently of a polynomial length envelope. -/
def WitnessPrefixObligation {Call : Type} (specification : MachineSpecification Call)
    (prefixLength : Call → ℕ) : Prop :=
  ∀ call witness,
    specification.value call witness =
      specification.value call (witness.take (prefixLength call))

/-- `prop:time`, paper/paper.tex: the exact three-term envelope.
This definition is a target bound, not a theorem about an implementation. -/
def propTimeEnvelope (n k Q Jmax lam exponent : ℕ) : ℕ :=
  2 ^ (n - k) * n ^ (2 * Jmax + exponent) +
    2 ^ (n - k) * Q * n ^ exponent + 2 ^ (10 * k + exponent * lam)

/-- `prop:time`, paper/paper.tex: proving this ledger is a separate
obligation from proving that the displayed envelope is eventually fast. -/
def LedgerObligation {Call : Type} (encoding : CallEncoding Call)
    (admitted : Call → Prop) (k Q Jmax lam : Call → ℕ)
    (specification : MachineSpecification Call) : Prop :=
  ∃ exponent onset : ℕ, ∀ call, onset ≤ encoding.arity call → admitted call →
    ∀ witness, specification.budget call witness ≤
      propTimeEnvelope (encoding.arity call) (k call) (Q call) (Jmax call) (lam call) exponent

/-- `thm:counter`, paper/paper.tex: temporary data-codec dock to the
proved gate interface; this does not supply quartic admission or a machine. -/
def gatesEncoding : CallEncoding NearCubicGates.Close.Interfaces.Call where
  arity := fun call => call.n
  word := NearCubicGates.Close.Interfaces.callWord

/-- `prop:time`, paper/paper.tex: regression dock to the existing
`Counter.program` field, without assuming that it is the quartic counter. -/
def gatesSpecification {B1 B2 : ℕ}
    (counter : NearCubicGates.Close.Interfaces.Counter B1 B2) :
    MachineSpecification NearCubicGates.Close.Interfaces.Call where
  value := counter.value
  budget := counter.budget

/-- `prop:time`, paper/paper.tex: the legacy codec/program dock is
definitionally exact.  No new quartic program is constructed here. -/
def gatesProgramDock {B1 B2 : ℕ}
    (counter : NearCubicGates.Close.Interfaces.Counter B1 B2) :
    WordFunction (NearCubicGates.Close.Interfaces.Call × List Bool)
      (requestWord gatesEncoding)
      (fun request => intervalWord (counter.value request.1 request.2))
      (fun request => counter.budget request.1 request.2) :=
  counter.program

/-- `prop:time`, paper/paper.tex: the fast-field shape is preserved;
the quartic budget proof must later be supplied by the new assembly. -/
def gatesFastType {B1 B2 : ℕ}
    (counter : NearCubicGates.Close.Interfaces.Counter B1 B2) : Prop :=
    FastObligation gatesEncoding (NearCubicGates.Close.Interfaces.Call.Admitted B1 B2)
      NearCubicGates.Target.mu (gatesSpecification counter)

end NearQuarticWires.Machine
