import Proof.Quartic.Transfer.Frontier4
import Proof.Gates.Transfer.Frontier
import Proof.Gates.Transfer.RecoveryTarget

/-!
# The weak-machine closure for the wire measure (paper App. A, §§A.3–A.6)

`GateClosure4 s P ε` is the base's `GateClosure` (the parameters `g` of the native family, the weak machine `M`, its
running time and its one-sided error, imported from `Proof.Gates.Interfaces.Transfer`) together with the native wire
cap `b(q)` and the completeness of `M` for target circuits measured by wires:
* `wbudget` is `b(q)` up to constant factors: `η 𝒜₄(q) ≤ b(q) ≤ q⁴` eventually (`lem:ae-cap` (i), paper/paper.tex);
* `wcomplete` is `lem:ae-table`'s branch construction: a `SYM∘THR` circuit with at most `b(q)` wires
  that agrees with the hard table of a CHECK-passing tautological pair on a `1 − γ/5 + ε` fraction makes `M` accept.

From such a closure the native family is hard for every circuit below the cap (`caseOnePart4`: `lem:ae-amplified`; `caseTwoPart4`: `lem:ae-table`), and the schedule turns `b(q)` into the cap `𝒜₄(m)/K` at the native
length `m` (`schedulePart4`). The `E^NP` recovery of the padded family is the base's (`RecoveryPart`, imported from
`Proof.Gates.Transfer.RecoveryTarget`): it involves no target circuit.
-/

set_option autoImplicit false

namespace NearQuarticWires.Transfer

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.RecoveryPipeline NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicWires.RepairSource.CloseoutCaseOne NearCubicGates.Target
open NearCubicWires.OuterPCPRecovery NearCubicWires.RecoveryScheduleEnvelope NearCubicWires.PhysicalRecovery
open NearCubicGates.Close NearCubicGates.Close.Transfer NearCubicGates.Close.Gadget

variable {s : GateSources} {P : ThreeQueryPCPP} {ε : ℝ}

/-- The weak-machine closure for the wire measure. -/
structure GateClosure4 (s : GateSources) (P : ThreeQueryPCPP) (ε : ℝ) where
  base : GateClosure s P ε
  /-- The native wire cap `b(q)`. -/
  wbudget : ℕ → ℕ
  wLower : ∃ η : ℝ, 0 < η ∧ ∃ q0 : ℕ, ∀ q, q0 ≤ q → η * A4 q ≤ (wbudget q : ℝ)
  wUpper : ∃ q1 : ℕ, ∀ q, q1 ≤ q → wbudget q ≤ q ^ 4
  /-- `lem:ae-table`: an approximator of the hard table within the wire cap makes the weak machine accept. -/
  wcomplete : ∃ onset : ℕ, ∀ ν : ℕ, onset ≤ ν → ∀ z : BitInput (2 ^ ν),
    ∀ B : Outer.OuterGuess (base.g.width s ν), B.src.size ≤ base.g.bound s ν → B.pf.size ≤ base.g.bound s ν →
    Outer.Check ν z B.src →
    ∀ hD : ∀ x, (base.g.D s ν B).D.eval x = true,
    ∀ C : SymmetricThresholdCircuit
        ((base.g.D s ν B).n + clauseWidth base.g.clauseDegree (base.g.width s ν) + base.g.positionLog),
      C.wireCount ≤ wbudget (base.g.width s ν) →
      1 - (P.gamma : ℝ) / 5 + ε ≤ NearCubicWires.agreement C.eval
        (hardTable P (base.g.D s ν B) hD (clauseWidth base.g.clauseDegree (base.g.width s ν)) base.g.positionLog) →
      base.M.accepts (2 ^ ν) z

/-! ## The three parts -/

/-- The schedule: the length dilation, and the cap `𝒜₄(m)/K` at the native length `m` lies below `b(q)`. -/
def SchedulePart4 (c : GateClosure s P ε) (wb : ℕ → ℕ) : Prop :=
  SelectionFacts c ∧ ∃ K : ℕ, 0 < K ∧ ∃ B : ℕ, 0 < B ∧ ∃ onset : ℕ,
    (∀ n, onset ≤ n → n ≤ B * c.g.nativeLength s n) ∧
    (∀ n, onset ≤ n → ∀ w : ℕ, (w : ℝ) ≤ A4 (c.g.nativeLength s n) / K →
      w ≤ wb (c.g.width s (c.g.selected s n)))

/-- Hardness of the native function for circuits below the wire cap, in one case of the canonical choices. -/
def CasePart4 (c : GateClosure s P ε) (wb : ℕ → ℕ) (small : Bool) : Prop :=
  SelectionFacts c → ∃ onset : ℕ, ∀ n, onset ≤ n → (c.Small n ↔ small = true) →
    ∀ C : SymmetricThresholdCircuit (c.g.nativeLength s n),
      C.wireCount ≤ wb (c.g.width s (c.g.selected s n)) →
      NearCubicWires.agreement C.eval (c.nativeFn n) < 1 - (P.gamma : ℝ) / 5 + ε

theorem frontier4_of_parts (c : GateClosure s P ε) (wb : ℕ → ℕ) (hs : SchedulePart4 c wb)
    (h1 : CasePart4 c wb false) (h2 : CasePart4 c wb true) (hr : RecoveryPart c) :
    Nonempty (NativeFrontier4 (P.gamma : ℝ) ε) := by
  classical
  obtain ⟨hsel, K, hK, B, hB, o0, hlen, hbud⟩ := hs
  obtain ⟨o1, hone⟩ := h1 hsel
  obtain ⟨o2, htwo⟩ := h2 hsel
  refine ⟨{ q := c.g.nativeLength s, q_le := c.g.nativeLength_le s, native := c.nativeFn,
            budgetConstant := K, budgetPositive := hK, dilation := B, dilationPositive := hB,
            onset := max o0 (max o1 o2),
            lengthBound := fun n hn => hlen n (le_trans (le_max_left _ _) hn),
            hard := ?_, ordinaryRecovery := hr }⟩
  intro n hn C hC
  have h0 : o0 ≤ n := le_trans (le_max_left _ _) hn
  have h1n : o1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have h2n : o2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hw := hbud n h0 C.wireCount hC
  by_cases hsmall : c.Small n
  · exact htwo n h2n (by simp [hsmall]) C hw
  · exact hone n h1n (by simp [hsmall]) C hw

/-! ## Schedule -/

theorem schedulePart4 (c : GateClosure s P ε) (wb : ℕ → ℕ)
    (hlow : ∃ η : ℝ, 0 < η ∧ ∃ q0 : ℕ, ∀ q, q0 ≤ q → η * A4 q ≤ (wb q : ℝ)) : SchedulePart4 c wb := by
  classical
  have hamp := c.ready.ampPos
  obtain ⟨η, hη, q0, hq0⟩ := hlow
  set C : ℕ := c.g.ampFactor * (1 + 2 * c.g.clauseDegree + c.g.positionLog) with hC
  set K : ℕ := ⌈(C : ℝ) ^ 4 / η⌉₊ + 1 with hKdef
  have hKpos : 0 < K := Nat.succ_pos _
  have hK : (C : ℝ) ^ 4 ≤ η * K := by
    have h1 : (C : ℝ) ^ 4 / η ≤ ⌈(C : ℝ) ^ 4 / η⌉₊ := Nat.le_ceil _
    have h2 : (⌈(C : ℝ) ^ 4 / η⌉₊ : ℝ) ≤ K := by rw [hKdef]; push_cast; linarith
    have h3 : (C : ℝ) ^ 4 / η ≤ K := h1.trans h2
    rwa [div_le_iff₀ hη, mul_comm] at h3
  have hsel := selectionFacts c
  obtain ⟨oL, hL⟩ := lengthBound c
  obtain ⟨oS, hS⟩ := hsel.2
  obtain ⟨oB, hB⟩ := hsel.1 (max q0 4)
  refine ⟨hsel, K, hKpos, 5, by norm_num, max oL (max oS oB), fun n hn => hL n (le_trans (le_max_left _ _) hn), ?_⟩
  intro n hn w hw
  obtain ⟨-, -, hlen⟩ := hS n (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn)
  have hνbig := hB n (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn)
  set ν := c.g.selected s n
  set q := c.g.width s ν
  have hqν : ν + 1 ≤ q := c.g.width_lower s ν
  have hq4 : 4 ≤ q := by have := le_max_right q0 4; omega
  have hqq0 : q0 ≤ q := by have := le_max_left q0 4; omega
  have hqm : q ≤ c.g.nativeLength s n := by
    rw [hlen]
    unfold GateParams.coreArity GateParams.tableArity
    calc q ≤ q + clauseWidth c.g.clauseDegree q + c.g.positionLog := by omega
      _ ≤ c.g.ampFactor * _ := Nat.le_mul_of_pos_left _ hamp
  have hmC : c.g.nativeLength s n ≤ C * q := by rw [hlen]; exact coreArity_le_linear s c.g ν
  have hdil := A4_dilation hq4 hqm hmC
  have hKr : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hA0 := A4_nonneg q
  have hreal : (w : ℝ) ≤ η * A4 q := by
    calc (w : ℝ) ≤ A4 (c.g.nativeLength s n) / K := hw
      _ ≤ (C : ℝ) ^ 4 * A4 q / K := div_le_div_of_nonneg_right hdil hKr.le
      _ ≤ η * K * A4 q / K := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hK hA0) hKr.le
      _ = η * A4 q := by field_simp
  have := hreal.trans (hq0 q hqq0)
  exact_mod_cast this

/-! ## Case 2 (`lem:ae-table`) -/

theorem caseTwoPart4 (c : GateClosure4 s P ε) : CasePart4 c.base c.wbudget true := by
  classical
  intro hsel
  let H := s.hierarchy (fun n => n ^ (c.base.g.k + 2)) c.base.g.clock
  obtain ⟨refOnset, refReady⟩ := refuterYes H.joint c.base.M c.base.littleO c.base.oneSided
  obtain ⟨cOnset, hcomp⟩ := c.wcomplete
  obtain ⟨o, hfacts⟩ := hsel.2
  obtain ⟨n0, hn0⟩ := hsel.1 (max cOnset refOnset)
  refine ⟨max o n0, fun n hn hsm C hC => ?_⟩
  have hsmall : c.base.Small n := hsm.mpr rfl
  have hon : o ≤ n := le_trans (le_max_left _ _) hn
  have hn0' : n0 ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨hν1, hνsrc, hlen⟩ := hfacts n hon
  have hνbig := hn0 n hn0'
  set ν := c.base.g.selected s n with hνdef
  have hνc : cOnset ≤ ν := le_trans (le_max_left _ _) hνbig
  have hνr : refOnset ≤ 2 ^ ν :=
    le_trans (le_max_right _ _) (le_trans hνbig (Nat.lt_two_pow_self).le)
  have hreject : ¬ c.base.M.accepts (2 ^ ν) (c.base.input n) := (refReady (2 ^ ν) hνr).1
  set B := c.base.g.selectedPair s ν (c.base.input n) hsmall with hBdef
  have hD := c.base.g.selected_taut s ν (c.base.input n) hsmall
  have hsrc : B.src.size ≤ c.base.g.bound s ν :=
    (RecoveryChoice.oracleSelector (c.base.g.checkPCP s ν (c.base.input n)) c.base.g.degree (c.base.input n)
      hsmall.1).sizeBounded
  have hpf : B.pf.size ≤ c.base.g.bound s ν :=
    (RecoveryChoice.oracleSelector _ c.base.g.degree (c.base.input n) hsmall.2.2.2).sizeBounded
  have hcheck : Outer.Check ν (c.base.input n) B.src :=
    (ENP.unitOuter_check ν _ _ (c.base.input n) (c.base.input n) _ (fun _ => false)).mp
      ((RecoveryChoice.oracleSelector (c.base.g.checkPCP s ν (c.base.input n)) c.base.g.degree (c.base.input n)
        hsmall.1).accepts (fun _ => false))
  set cl := clauseWidth c.base.g.clauseDegree (c.base.g.width s ν)
  have hDn : (c.base.g.D s ν B).n = c.base.g.width s ν := rfl
  have hfit : (c.base.g.D s ν B).n + cl + c.base.g.positionLog ≤ c.base.g.nativeLength s n := by
    rw [hlen, hDn]
    unfold GateParams.coreArity GateParams.tableArity
    exact Nat.le_mul_of_pos_left _ c.base.ready.ampPos
  have hnative : c.base.nativeFn n = padCore (hardTable P (c.base.g.D s ν B) hD cl c.base.g.positionLog) hfit := by
    simp only [GateClosure.nativeFn, GateParams.native]
    rw [if_pos ⟨hν1, hνsrc⟩]
    exact gateCore_small s c.base.g P _ ν (c.base.input n) cl c.base.g.positionLog _ hsmall hfit
  obtain ⟨small, hw, hag⟩ := exists_wire_restriction hfit C (hardTable P (c.base.g.D s ν B) hD cl c.base.g.positionLog)
  rw [hnative]
  refine lt_of_le_of_lt hag ?_
  by_contra hge
  exact hreject (hcomp ν hνc (c.base.input n) B hsrc hpf hcheck hD small (hw.trans hC) (not_lt.mp hge))

end NearQuarticWires.Transfer
