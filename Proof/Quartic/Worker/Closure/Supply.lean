import Proof.Quartic.Worker.Prelude
import Proof.Quartic.Worker.Closure.Obligations
import Proof.CaseAnalysis.WeakSelectedRuntime
import Proof.Circuits.PolynomialOrdinaryClock
import Proof.Gates.Transfer.Schedule
import Proof.Gates.Transfer.LenFit
import Proof.Quartic.Worker.Worker.NativeLower

/-! Adapted from `Proof.Gates.Closure.Supply` of the near-cubic gate proof, with the wire measure and the cap 𝒜₄: the counter is `Counter4` (`NearQuarticWires.Worker4.Counter`). -/

set_option autoImplicit false

namespace NearQuarticWires.Worker4.Closure
open NearCubicGates NearCubicGates.Close NearCubicGates.Close.Closure

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.CloseoutWitness
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutLanguage NearCubicWires.RepairSource.CloseoutWeakRuntime
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer NearCubicGates.Close.Worker NearQuarticWires.Worker4.Worker
open NearCubicGates.PublishedSources.PCPP

theorem gate_littleO (s : GateSources) (g : GateParams)
    (M : OrdinaryWeakMachine) (A B a sigma : ℕ) (hot : ℕ → ℕ)
    (ha : a ≤ g.k + 1) (hs : Outer.apad s.mw (g.sv s) + 1 ≤ sigma)
    (bound : ∃ onset, ∀ N, onset ≤ N →
      M.runtime N ≤ A * (N + 1) ^ a + hot N ∧ hot N * (width s g N) ^ sigma ≤ B * 2 ^ (width s g N)) :
    OrdinaryLittleO M (fun n => n ^ (g.k + 2)) := by
  have hA : 1 ≤ Outer.apad s.mw (g.sv s) := by unfold Outer.apad; omega
  apply littleO_of_split M g.k A B (3 * 12 ^ Outer.apad s.mw (g.sv s)) a (Outer.apad s.mw (g.sv s)) sigma
    (width s g) hot ha hs
  · intro m
    exact ⟨2 ^ m, fun N hN => gate_nativeWidth_ge s g m N hN⟩
  · obtain ⟨onset, hbound⟩ := bound
    refine ⟨max onset 1, ?_⟩
    intro N hn
    obtain ⟨hr, hh⟩ := hbound N ((Nat.le_max_left _ _).trans hn)
    exact ⟨hr, hh, Outer.widthOf_table g.k _ N ((Nat.le_max_right _ _).trans hn) hA⟩

/-- `𝒜₃ → ∞`, and eventually `0 ≤ 𝒜₃(q) ≤ q³` and `𝒜₃(q) ≤ 𝒜₁(q)`. -/
def AsymptoticsFacts : Prop :=
  (∀ M : ℝ, ∃ q0 : ℕ, ∀ q, q0 ≤ q → M ≤ A3 q) ∧
    ∃ q0 : ℕ, ∀ q, q0 ≤ q → 0 ≤ A3 q ∧ A3 q ≤ (q : ℝ) ^ 3 ∧ A3 q ≤ A1 q

def ClauseRoom (s : GateSources) (P : ThreeQueryPCPP) : Prop :=
  ∀ g : GateParams, ∃ d onset : ℕ, 1 ≤ d ∧ ∀ (N : ℕ) (x : BitInput N) (B : Outer.OuterGuess (width s g N)),
    B.pf.size ≤ RecoveryScheduleEnvelope.oracleSizeBound g.degree (width s g N) → onset ≤ width s g N → 2 ≤ N →
    (P.output (checkedCircuit P.code (substituted s g x B))).randomBits ≤ clauseWidth d (width s g N)

theorem list_ofFn_getD (bits : List Bool) {m : ℕ} (h : bits.length = m) :
    List.ofFn (fun i : Fin m => bits.getD i.val false) = bits := by
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2
    simp [List.getElem?_eq_getElem h2]

/-! The outer PCP and the refuter are used, never unfolded, in the assembly below. -/
attribute [local irreducible] GateSources.hierarchy

/-- Transport of the Case 2 data along an equality of outer verifiers. -/
theorem hardTable_transport (P : ThreeQueryPCPP) {D1 D2 : NearCubicWires.Bindings.CLW20Lemma311.Circuit} (h : D1 = D2)
    (hD2 : ∀ x, D2.D.eval x = true) (cl pl : ℕ) (C2 : NearCubicGates.Target.WeightedSymmetricCircuit (D2.n + cl + pl)) :
    ∃ (hD1 : ∀ x, D1.D.eval x = true) (C1 : NearCubicGates.Target.WeightedSymmetricCircuit (D1.n + cl + pl)),
      C1.topWeight = C2.topWeight ∧
      NearCubicGates.FiniteAverages.agreement C1.eval (hardTable P D1 hD1 cl pl) =
        NearCubicGates.FiniteAverages.agreement C2.eval (hardTable P D2 hD2 cl pl) := by
  subst h
  exact ⟨hD2, C2, rfl, rfl⟩

/-- At `N = 2^ν` the worker's outer verifier is the transfer side's `D_B`. -/
theorem substituted_pow (s : GateSources) (g : GateParams) (ν : ℕ) (z : BitInput (2 ^ ν))
    (B : Outer.OuterGuess (width s g (2 ^ ν))) : substituted s g z B = g.D s ν B := by
  show Outer.Dat s.mw (g.sv s) (Nat.log 2 (2 ^ ν)) B = Outer.Dat s.mw (g.sv s) ν B
  rw [Nat.log_pow (by norm_num)]

end NearQuarticWires.Worker4.Closure
