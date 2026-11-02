import Proof.Quartic.Transfer.Main4
import Proof.Quartic.Worker.Worker.CompleteWire
import Proof.Quartic.Worker.WorkerArith.SupplyWire
import Proof.Quartic.Worker.Setup.Supply
import Proof.Quartic.Worker.Closure.Asymptotics

/-!
# The wire-measured closure from the counter and the weak machine (paper §A.2 and §A.7)

`closureSupply4_of`: a wire counter at `B₁ = B₂ = 1` (`CounterExists4`) gives a wire-measured closure at every
`0 < ε < γ/5`, with the weak machine of §A.4 for that counter (`NearQuarticWires.Worker4.WorkerArith.workerSupply4`). The parameters are those of §A.2: the radius `ω ≤ min(ε/128, 1/16)`, a threshold `ε < ε_T < 2ε`, the native wire cap
`b(q) = ⌊η 𝒜₄(q)⌋` with `η ≤ min(a ω/2, 1/2)` (so `2b(q) ≤ a ω 𝒜₄(q)` and `b(q) ≤ q⁴`, `lem:ae-cap` (i), (ii)), and the
parameters of the native family in the order of §A.7. The base's closure (with its own weighted budget, imported from
`Proof.Gates.Interfaces.Transfer`) is obtained from the wire completeness: a weighted circuit with at most
`η' 𝒜₃(q)` top weight is a `SYM∘THR` circuit with at most `η' 𝒜₃(q) (m + 1) ≤ η 𝒜₄(q)` wires on the table's `m`
inputs (`toSymmetric_wireCount`, `qA3_le_A4`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Transfer

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.CloseoutWitness
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutLanguage NearCubicWires.RepairSource.CloseoutWeakRuntime
open NearCubicGates.Close NearCubicGates.Close.Interfaces NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearQuarticWires.Worker4.Worker NearQuarticWires.Worker4.Closure NearCubicGates.PublishedSources.PCPP NearCubicGates.Target

/-! ## `𝒜₄` against `𝒜₃` and `q⁴` -/

theorem qA3_le_A4 {q : ℕ} (hq : 4 ≤ q) : (q : ℝ) * A3 q ≤ A4 q := by
  unfold A3 A4
  have hL : (2 : ℝ) ≤ ((lambda q : ℕ) : ℝ) := by exact_mod_cast NearCubicGates.Close.Transfer.lambda_ge_two hq
  have hM : (1 : ℝ) ≤ ((mu q : ℕ) : ℝ) := by exact_mod_cast NearCubicGates.Close.Transfer.mu_ge_one hq
  have hML : ((mu q : ℕ) : ℝ) ≤ ((lambda q : ℕ) : ℝ) := by exact_mod_cast NearQuarticWires.Worker4.Closure.mu_le_lambda q
  set L : ℝ := ((lambda q : ℕ) : ℝ)
  set M : ℝ := ((mu q : ℕ) : ℝ)
  have hL0 : 0 < L := by linarith
  have hM0 : 0 < M := by linarith
  have e1 : L ^ ((21 : ℝ) / 4) = L ^ ((17 : ℝ) / 4) * L := by
    rw [← Real.rpow_add_one hL0.ne']; norm_num
  have e2 : M ^ ((15 : ℝ) / 2) = M ^ (7 : ℕ) * M ^ ((1 : ℝ) / 2) := by
    rw [show (15 : ℝ) / 2 = ((7 : ℕ) : ℝ) + 1 / 2 by norm_num, Real.rpow_add hM0, Real.rpow_natCast]
  have hs : M ^ ((1 : ℝ) / 2) ≤ L := by
    have := Real.rpow_le_rpow_of_exponent_le hM (show (1 : ℝ) / 2 ≤ 1 by norm_num)
    rw [Real.rpow_one] at this
    linarith
  have ha : 0 < L ^ ((17 : ℝ) / 4) := Real.rpow_pos_of_pos hL0 _
  have hs0 : 0 < M ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hM0 _
  have hM7 : 0 < M ^ (7 : ℕ) := pow_pos hM0 7
  rw [e1, e2, mul_div_assoc', ← pow_succ']
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  calc L ^ ((17 : ℝ) / 4) * (M ^ (7 : ℕ) * M ^ ((1 : ℝ) / 2))
      = L ^ ((17 : ℝ) / 4) * M ^ (7 : ℕ) * M ^ ((1 : ℝ) / 2) := by ring
    _ ≤ L ^ ((17 : ℝ) / 4) * M ^ (7 : ℕ) * L := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = L ^ ((17 : ℝ) / 4) * L * M ^ 7 := by ring

/-- `lem:ae-cap` (i): `𝒜₄(q) ≤ q⁴`. -/
theorem A4_le_pow4 {q : ℕ} (hq : 4 ≤ q) : A4 q ≤ (q : ℝ) ^ 4 := by
  rw [A4_eq]
  have hL : (1 : ℝ) ≤ ((lambda q : ℕ) : ℝ) := by
    have := NearCubicGates.Close.Transfer.lambda_ge_two hq
    exact_mod_cast (show 1 ≤ lambda q by omega)
  have hM : (1 : ℝ) ≤ ((mu q : ℕ) : ℝ) := by exact_mod_cast NearCubicGates.Close.Transfer.mu_ge_one hq
  have h1 : 1 ≤ logDen q := by
    unfold logDen
    exact one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hL (by norm_num)) (Real.one_le_rpow hM (by norm_num))
  exact div_le_self (by positivity) h1

/-- The native wire cap `b(q) = ⌊η 𝒜₄(q)⌋` (§A.2, with `η = η₀ ε`). -/
noncomputable def wireBudget (η : ℝ) (q : ℕ) : ℕ := ⌊η * A4 q⌋₊

/-- Transport of the Case 2 data along an equality of outer verifiers. -/
theorem hardTable_transport4 (P : ThreeQueryPCPP) {D1 D2 : NearCubicWires.Bindings.CLW20Lemma311.Circuit} (h : D1 = D2)
    (hD2 : ∀ x, D2.D.eval x = true) (cl pl : ℕ) (C2 : SymmetricThresholdCircuit (D2.n + cl + pl)) :
    ∃ (hD1 : ∀ x, D1.D.eval x = true) (C1 : SymmetricThresholdCircuit (D1.n + cl + pl)),
      C1.wireCount = C2.wireCount ∧
      NearCubicWires.agreement C1.eval (hardTable P D1 hD1 cl pl) =
        NearCubicWires.agreement C2.eval (hardTable P D2 hD2 cl pl) := by
  subst h
  exact ⟨hD2, C2, rfl, rfl⟩

/-- A weighted circuit with top weight at most `η' 𝒜₃(q)` on `m < C q` inputs is a `SYM∘THR` circuit with at most
`⌊η 𝒜₄(q)⌋` wires, when `η' C ≤ η`. -/
theorem toSymmetric_wire_le {m q Cm : ℕ} (C0 : NearCubicGates.Target.WeightedSymmetricCircuit m) (hq4 : 4 ≤ q)
    (hm : m + 1 ≤ Cm * q) {η' η : ℝ} (h2 : (C0.topWeight : ℝ) ≤ η' * A3 q) (hA30 : 0 ≤ A3 q) (hη'0 : 0 ≤ η')
    (hη'C : η' * Cm ≤ η) (hη0 : 0 ≤ η) : (toSymmetric C0).wireCount ≤ ⌊η * A4 q⌋₊ := by
  apply Nat.le_floor
  have h1 := toSymmetric_wireCount C0
  have h3 := qA3_le_A4 hq4
  have hmr : ((m + 1 : ℕ) : ℝ) ≤ (Cm : ℝ) * q := by exact_mod_cast hm
  have hw : ((toSymmetric C0).wireCount : ℝ) ≤ (C0.topWeight : ℝ) * ((m + 1 : ℕ) : ℝ) := by exact_mod_cast h1
  calc ((toSymmetric C0).wireCount : ℝ) ≤ (C0.topWeight : ℝ) * ((m + 1 : ℕ) : ℝ) := hw
    _ ≤ (η' * A3 q) * ((Cm : ℝ) * q) := mul_le_mul h2 hmr (by positivity) (by positivity)
    _ = (η' * Cm) * ((q : ℝ) * A3 q) := by ring
    _ ≤ η * A4 q := mul_le_mul hη'C h3 (by positivity) hη0

/-! The outer PCP and the refuter are used, never unfolded, in the assembly below. -/
attribute [local irreducible] GateSources.hierarchy

/-- **The wire-measured closures** from the wire counter. -/
theorem closureSupply4_of (hC : CounterExists4) : ClosureSupply4 := by
  classical
  intro s P ε hε hεγ
  obtain ⟨ctr⟩ := hC 1 1 one_pos one_pos
  obtain ⟨aC, haC, onsetC, hcomp⟩ := ctr.complete
  obtain ⟨hgrow, qA, hAq⟩ := NearQuarticWires.Worker4.Closure.asymptoticsFacts
  have hR : ∀ s P, ClauseRoom s P := clauseRoom
  have hγ1 : (P.gamma : ℝ) < 1 := by exact_mod_cast P.gamma_lt_one
  have hε1 : ε < 1 := by linarith
  -- the radius `ω ≤ min(ε/128, 1/16)`
  obtain ⟨ω, hω0, hωlt⟩ := exists_rat_btwn (show (0 : ℝ) < min (ε / 128) (1 / 16) by positivity)
  have hω0' : (0 : ℚ) < ω := by exact_mod_cast hω0
  have hωε : (ω : ℝ) ≤ ε / 128 := le_of_lt (lt_of_lt_of_le hωlt (min_le_left _ _))
  have hω16 : ω ≤ 1 / 16 := by
    have h := le_of_lt (lt_of_lt_of_le hωlt (min_le_right _ _))
    have h' : ((ω : ℚ) : ℝ) ≤ ((1 / 16 : ℚ) : ℝ) := by push_cast; exact h
    exact_mod_cast h'
  -- the machine threshold `ε < ε_T < 2ε`
  obtain ⟨εT, hεT1, hεT2⟩ := exists_rat_btwn (show ε < 2 * ε by linarith)
  have hεT0 : (0 : ℝ) < εT := by linarith
  -- the native wire cap `b = ⌊η 𝒜₄⌋` with `0 < η ≤ min(aω/2, 1/2)`
  set η : ℝ := min (aC * ω / 2) (1 / 2) with hηdef
  have hη0 : 0 < η := by positivity
  have hηa : η ≤ aC * ω / 2 := min_le_left _ _
  have hη1 : η ≤ 1 / 2 := min_le_right _ _
  set wb : ℕ → ℕ := wireBudget η with hwbdef
  have hwle : ∀ q, (wb q : ℝ) ≤ η * A4 q := fun q =>
    Nat.floor_le (mul_nonneg hη0.le (A4_nonneg q))
  have hwU : ∀ q, 4 ≤ q → wb q ≤ q ^ 4 := by
    intro q hq
    have h1 := hwle q
    have h2 := A4_le_pow4 hq
    have h3 := A4_nonneg q
    have : (wb q : ℝ) ≤ (q : ℝ) ^ 4 := by nlinarith
    exact_mod_cast this
  obtain ⟨d0, hWs⟩ := NearQuarticWires.Worker4.WorkerArith.workerSupply4
    (NearQuarticWires.Worker4.Setup.setupSupply_of_subst NearCubicGates.Close.Succinct.SubstMachine.substReady)
    s P 1 1 ctr wb εT ω ⟨4, hwU⟩ hω0'
  -- the position count `P = 2^{pl} > max(128/ε, 8)`
  obtain ⟨pl, hpl⟩ := pow_unbounded_of_one_lt (max (128 / ε) 8) (by norm_num : (1 : ℝ) < 2)
  have hpl8 : (8 : ℝ) < 2 ^ pl := lt_of_le_of_lt (le_max_right _ _) hpl
  have hpl128 : 128 / ε < 2 ^ pl := lt_of_le_of_lt (le_max_left _ _) hpl
  have hP : 128 ≤ ε * ((2 ^ pl : ℕ) : ℝ) := by
    push_cast
    have := (div_lt_iff₀ hε).1 hpl128
    linarith
  have hP5 : 5 ≤ 2 ^ pl := by
    have : (5 : ℝ) < 2 ^ pl := by linarith
    exact_mod_cast this.le
  have hpl1 : 1 ≤ pl := by
    rcases Nat.eq_zero_or_pos pl with h | h
    · subst h; norm_num at hpl8
    · exact h
  -- the degrees and the parameters in the order of §A.7: G, then G′, then the clock, then d_G
  set degree := 17 * s.amplification.stvExponent with hdeg
  obtain ⟨lenRoot, hlenFit⟩ := Transfer.lenFit s degree
  set g0 : GateParams := ⟨d0 + 1, PolynomialClock.ordinaryClock (d0 + 1), degree, lenRoot, 0, pl,
    max 1 (selectedAmplifier s.amplification degree).arityCoefficient, 0⟩ with hg0
  obtain ⟨d, onsetR, hd1, hRoom⟩ := hR s P g0
  set g : GateParams := { g0 with clauseDegree := d } with hg
  obtain ⟨W⟩ := hWs g (show d0 ≤ d0 + 1 + 1 by omega)
  obtain ⟨onsetF, hfits⟩ := W.complete
  obtain ⟨fitOnset, hfitν⟩ := hlenFit g rfl rfl
  -- the base's weighted budget `budgetOf η'` with `η' (2 + 2 d_G + log P) ≤ η`
  set Cm : ℕ := 2 + 2 * g.clauseDegree + g.positionLog with hCm
  have hCm0 : (0 : ℝ) < Cm := by positivity
  obtain ⟨η', hη'0r, hη'lt⟩ := exists_rat_btwn (show (0 : ℝ) < η / Cm by positivity)
  have hη'0 : (0 : ℚ) < η' := by exact_mod_cast hη'0r
  have hη'C : (η' : ℝ) * Cm ≤ η := by
    have := (lt_div_iff₀ hCm0).1 hη'lt
    linarith
  have hη'1 : (η' : ℝ) ≤ 1 / 2 := by
    have hC1 : (1 : ℝ) ≤ Cm := by rw [hCm]; push_cast; linarith [(by positivity : (0 : ℝ) ≤ (g.positionLog : ℝ))]
    nlinarith
  set budget : ℕ → ℕ := NearCubicGates.Close.Closure.budgetOf η' with hbudget
  have hqA4 : ∀ q, max qA 4 ≤ q → 4 ≤ q ∧ qA ≤ q := fun q hq => ⟨(le_max_right _ _).trans hq,
    (le_max_left _ _).trans hq⟩
  have hbud_le : ∀ q, max qA 4 ≤ q → (budget q : ℝ) ≤ η' * A3 q := fun q hq =>
    (NearCubicGates.Close.Closure.budgetOf_bounds η' hη'0 q (hqA4 q hq).1).1
  have hcubic : ∀ q, max qA 4 ≤ q → budget q ≤ q ^ 3 := by
    intro q hq
    obtain ⟨h0, h3, -⟩ := hAq q (hqA4 q hq).2
    have h := hbud_le q hq
    have hη'0' : (0 : ℝ) ≤ (η' : ℝ) := by exact_mod_cast hη'0.le
    have : (budget q : ℝ) ≤ (q : ℝ) ^ 3 := by nlinarith
    exact_mod_cast this
  -- eventual thresholds on the native width
  obtain ⟨qG, hqG⟩ := hgrow (4 / (η' : ℝ))
  set Q : ℕ := max (max (max 4 onsetC) (max (max qA 4) qG)) (max (max (Nat.ceil (1 / (ω : ℝ))) (ratWord ω).length) onsetR)
    with hQ
  -- the wire completeness of the weak machine (`lem:ae-table`)
  have wcomp : ∃ onset : ℕ, ∀ ν : ℕ, onset ≤ ν → ∀ z : BitInput (2 ^ ν),
      ∀ B : Outer.OuterGuess (g.width s ν), B.src.size ≤ g.bound s ν → B.pf.size ≤ g.bound s ν →
      Outer.Check ν z B.src →
      ∀ hD : ∀ x, (g.D s ν B).D.eval x = true,
      ∀ C : SymmetricThresholdCircuit
          ((g.D s ν B).n + clauseWidth g.clauseDegree (g.width s ν) + g.positionLog),
        C.wireCount ≤ wb (g.width s ν) →
        1 - (P.gamma : ℝ) / 5 + ε ≤ NearCubicWires.agreement C.eval
          (hardTable P (g.D s ν B) hD (clauseWidth g.clauseDegree (g.width s ν)) g.positionLog) →
        (Weak.machine W.worker W.htapes W.result W.fuel _
          (Weak.allInputRun_of_total W.worker W.htapes W.result W.fuel W.total)).accepts (2 ^ ν) z := by
    refine ⟨max (max (max Q onsetF) (Nat.ceil (1 / (εT : ℝ)))) (max fitOnset ((g.sv s).onset + 1)), ?_⟩
    intro ν hν z B hsrc hpf hcheck hD C0 hCw0 hagree0
    have hν' : max (max Q onsetF) (Nat.ceil (1 / (εT : ℝ))) ≤ ν := (le_max_left _ _).trans hν
    have hνfit : fitOnset ≤ ν := (le_max_left _ _).trans ((le_max_right _ _).trans hν)
    have hνsv : (g.sv s).onset + 1 ≤ ν := (le_max_right _ _).trans ((le_max_right _ _).trans hν)
    show (Weak.machine W.worker W.htapes W.result W.fuel _
      (Weak.allInputRun_of_total W.worker W.htapes W.result W.fuel W.total)).accepts (2 ^ ν) z
    apply (Weak.accepts_exact W.worker W.htapes W.result W.fuel _
      (Weak.allInputRun_of_total W.worker W.htapes W.result W.fuel W.total) (2 ^ ν) z).mpr
    have hνQ : Q ≤ ν := (le_max_left _ _).trans ((le_max_left _ _).trans hν')
    have hνF : onsetF ≤ ν := (le_max_right _ _).trans ((le_max_left _ _).trans hν')
    have hνε : Nat.ceil (1 / (εT : ℝ)) ≤ ν := (le_max_right _ _).trans hν'
    have hwid : ν + 1 ≤ width s g (2 ^ ν) := GateParams.width_lower s g ν
    have hqQ : Q ≤ width s g (2 ^ ν) := by omega
    have hq4 : 4 ≤ width s g (2 ^ ν) := le_trans (by
      rw [hQ]; exact (le_max_left 4 onsetC).trans ((le_max_left _ _).trans (le_max_left _ _))) hqQ
    have hqC : onsetC ≤ width s g (2 ^ ν) := le_trans (by
      rw [hQ]; exact (le_max_right 4 onsetC).trans ((le_max_left _ _).trans (le_max_left _ _))) hqQ
    have hqA' : max qA 4 ≤ width s g (2 ^ ν) :=
      ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _))).trans hqQ
    have hqA : qA ≤ width s g (2 ^ ν) := (le_max_left _ _).trans hqA'
    have hqω : Nat.ceil (1 / (ω : ℝ)) ≤ width s g (2 ^ ν) := le_trans (by
      rw [hQ]; exact (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))) hqQ
    have hqr : (ratWord ω).length ≤ width s g (2 ^ ν) := le_trans (by
      rw [hQ]; exact (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))) hqQ
    have hqR : onsetR ≤ width s g (2 ^ ν) := le_trans (by
      rw [hQ]; exact (le_max_right _ _).trans (le_max_right _ _)) hqQ
    have hn : 1 ≤ width s g (2 ^ ν) := by omega
    have hr1 : 1 ≤ ω * (width s g (2 ^ ν) : ℚ) ^ 1 := by
      have hq1 : (1 / (ω : ℝ)) ≤ width s g (2 ^ ν) := (Nat.le_ceil _).trans (by exact_mod_cast hqω)
      have hωq : (1 : ℝ) ≤ ω * width s g (2 ^ ν) := by
        rw [div_le_iff₀ hω0] at hq1; linarith
      have hpow : (width s g (2 ^ ν) : ℝ) ≤ (width s g (2 ^ ν) : ℝ) ^ 1 :=
        le_self_pow₀ (by exact_mod_cast hn) (by omega)
      have : (1 : ℝ) ≤ ω * (width s g (2 ^ ν) : ℝ) ^ 1 := by nlinarith
      exact_mod_cast this
    have hr3 : (ratWord ω).length ≤ width s g (2 ^ ν) ^ 1 :=
      hqr.trans (Nat.le_self_pow (by omega) _)
    have hb : (wb (width s g (2 ^ ν)) : ℝ) ≤ η * A4 (width s g (2 ^ ν)) := hwle _
    have hA0 := A4_nonneg (width s g (2 ^ ν))
    have hηA : 2 * η * A4 (width s g (2 ^ ν)) ≤ aC * (ω : ℝ) * A4 (width s g (2 ^ ν)) :=
      mul_le_mul_of_nonneg_right (by linarith [hηa]) hA0
    have hA4c : (2 * wb (width s g (2 ^ ν)) : ℝ) ≤ aC * (ω : ℝ) * A4 (width s g (2 ^ ν)) := by
      linarith [hb, hηA]
    have hb4 : wb (width s g (2 ^ ν)) ≤ width s g (2 ^ ν) ^ 4 := hwU _ hq4
    -- `ν = log₂ 2^ν`, and the set-up's guards on the pair
    have hnu : nu (2 ^ ν) = ν := Nat.log_pow (by norm_num) ν
    have hν1 : 1 ≤ nu (2 ^ ν) := by rw [hnu]; omega
    have hprec : (P.gamma : ℝ) / (Outer.instLength g.lenExp (nu (2 ^ ν)) : ℝ) < (εT : ℝ) := by
      rw [hnu]
      have hνr : (1 / (εT : ℝ)) ≤ ν := (Nat.le_ceil _).trans (by exact_mod_cast hνε)
      have hL : (ν : ℝ) ≤ (Outer.instLength g.lenExp ν : ℝ) := by
        have : ν ≤ Outer.instLength g.lenExp ν := by
          unfold Outer.instLength
          calc ν = ν ^ 1 := (pow_one ν).symm
            _ ≤ ν ^ (g.lenExp + 2) := Nat.pow_le_pow_right (by omega) (by omega)
        exact_mod_cast this
      have hLpos : (0 : ℝ) < (Outer.instLength g.lenExp ν : ℝ) := by
        exact_mod_cast Outer.instLength_pos (G := g.lenExp) ν (by omega)
      rw [div_lt_iff₀ hLpos]
      have h1 : 1 ≤ (εT : ℝ) * ν := by rw [div_le_iff₀ hεT0] at hνr; linarith
      calc (P.gamma : ℝ) < 1 := hγ1
        _ ≤ (εT : ℝ) * ν := h1
        _ ≤ (εT : ℝ) * (Outer.instLength g.lenExp ν : ℝ) := mul_le_mul_of_nonneg_left hL hεT0.le
    have hpair : PairOK s g z B := by
      refine ⟨by rw [hnu], by rw [hnu]; omega, by rw [hnu]; exact hfitν ν hνfit B.src hsrc, ?_⟩
      rw [hnu]
      exact (Outer.check_iff_checkAt ν z B.src).mp hcheck

    obtain ⟨hD1, C, hCt, hag⟩ := hardTable_transport4 P (substituted_pow s g ν z B) hD
      (clauseWidth g.clauseDegree (width s g (2 ^ ν))) g.positionLog C0
    have hCw : C.wireCount ≤ wb (width s g (2 ^ ν)) := hCt ▸ hCw0
    have hagree : 1 - (P.gamma : ℝ) / 5 + ε ≤ NearCubicWires.agreement C.eval
        (hardTable P (substituted s g z B) hD1 (clauseWidth g.clauseDegree (width s g (2 ^ ν))) g.positionLog) :=
      hag ▸ hagree0
    have hrb := hRoom (2 ^ ν) z B hpf hqR (by have := Nat.one_lt_two_pow (n := ν) (by omega); omega)
    obtain ⟨hguards, hsizeok, hU⟩ := approx_complete4 s P g z B hD1 C s.normalization hn ctr ω
      aC onsetC hcomp wb ε (εT : ℝ) hCw hagree hε hε1 hεγ (by linarith) hω0'.le hωε hP5 hP hq4 hqC hb4 hr1
      hω16 hr3 hA4c hsrc hpf hrb hν1 hprec hpair
    exact hfits (2 ^ ν) (hνF.trans (Nat.lt_two_pow_self).le) z _ hsizeok ⟨hguards, hU⟩
  -- the base's weighted completeness, from the wire completeness
  have bcomp : ∃ onset : ℕ, ∀ ν : ℕ, onset ≤ ν → ∀ z : BitInput (2 ^ ν),
      ∀ B : Outer.OuterGuess (g.width s ν), B.src.size ≤ g.bound s ν → B.pf.size ≤ g.bound s ν →
      Outer.Check ν z B.src →
      ∀ hD : ∀ x, (g.D s ν B).D.eval x = true,
      ∀ C : NearCubicGates.Target.WeightedSymmetricCircuit
          ((g.D s ν B).n + clauseWidth g.clauseDegree (g.width s ν) + g.positionLog),
        C.topWeight ≤ budget (g.width s ν) →
        1 - (P.gamma : ℝ) / 5 + ε ≤ NearCubicGates.FiniteAverages.agreement C.eval
          (hardTable P (g.D s ν B) hD (clauseWidth g.clauseDegree (g.width s ν)) g.positionLog) →
        (Weak.machine W.worker W.htapes W.result W.fuel _
          (Weak.allInputRun_of_total W.worker W.htapes W.result W.fuel W.total)).accepts (2 ^ ν) z := by
    obtain ⟨o, h⟩ := wcomp
    refine ⟨max o (max qA 4), fun ν hν z B hsrc hpf hcheck hD C0 hC0 hag0 =>
      h ν ((le_max_left _ _).trans hν) z B hsrc hpf hcheck hD (toSymmetric C0) ?_ ?_⟩
    · have hqν : ν + 1 ≤ g.width s ν := g.width_lower s ν
      have hqa : max qA 4 ≤ g.width s ν := by have := (le_max_right o (max qA 4)).trans hν; omega
      have hq4 : 4 ≤ g.width s ν := (hqA4 _ hqa).1
      have hcw := clause_linear g.clauseDegree (g.width s ν)
      have hm : (g.D s ν B).n + clauseWidth g.clauseDegree (g.width s ν) + g.positionLog + 1 ≤ Cm * g.width s ν := by
        show g.width s ν + clauseWidth g.clauseDegree (g.width s ν) + g.positionLog + 1 ≤ Cm * g.width s ν
        rw [hCm]
        have h1 : g.positionLog ≤ g.positionLog * g.width s ν := Nat.le_mul_of_pos_right _ (by omega)
        nlinarith
      have h2 : (C0.topWeight : ℝ) ≤ η' * A3 (g.width s ν) := by
        have : (C0.topWeight : ℝ) ≤ (budget (g.width s ν) : ℝ) := by exact_mod_cast hC0
        exact this.trans (hbud_le _ hqa)
      exact toSymmetric_wire_le C0 hq4 hm h2 (hAq _ (hqA4 _ hqa).2).1 (by exact_mod_cast hη'0.le) hη'C hη0.le
    · have hev : (toSymmetric C0).eval = C0.eval := funext (toSymmetric_eval C0)
      rw [hev, ← finiteAgreement_eq]
      exact hag0
  -- the wire cap's lower bound `b ≥ η𝒜₄/2` once `η𝒜₄ ≥ 2`
  have hwL : ∃ η₁ : ℝ, 0 < η₁ ∧ ∃ q0 : ℕ, ∀ q, q0 ≤ q → η₁ * A4 q ≤ (wb q : ℝ) := by
    obtain ⟨qG', hqG'⟩ := hgrow (2 / η)
    refine ⟨η / 2, by positivity, max (max qA 4) qG', fun q hq => ?_⟩
    have hqa : max qA 4 ≤ q := (le_max_left _ _).trans hq
    have hq4 : 4 ≤ q := (hqA4 q hqa).1
    have hA3 := hqG' q ((le_max_right _ _).trans hq)
    have h3 := qA3_le_A4 hq4
    have hA30 : 0 ≤ A3 q := (hAq q (hqA4 q hqa).2).1
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
    have hA4 : 2 / η ≤ A4 q := by nlinarith
    have hηA : 2 ≤ η * A4 q := by
      have := mul_le_mul_of_nonneg_left hA4 hη0.le
      rwa [mul_div_cancel₀ _ hη0.ne'] at this
    have hfl := Nat.sub_one_lt_floor (η * A4 q)
    show η / 2 * A4 q ≤ (⌊η * A4 q⌋₊ : ℝ)
    linarith
  refine ⟨{
    base := {
      g := g
      budget := budget
      ready := ⟨le_max_left _ _, ⟨(η' : ℝ) / 4, by positivity, max (max qA 4) qG, ?_⟩, ⟨max qA 4, hcubic⟩,
        le_refl _, le_max_right _ _, hpl1, hd1, ⟨fitOnset, hfitν⟩⟩
      M := Weak.machine W.worker W.htapes W.result W.fuel _
        (Weak.allInputRun_of_total W.worker W.htapes W.result W.fuel W.total)
      littleO := ?_
      oneSided := ?_
      complete := bcomp }
    wbudget := wb
    wLower := hwL
    wUpper := ⟨4, hwU⟩
    wcomplete := wcomp }⟩
  · -- budgetLower: `b ≥ η'𝒜₃/2 − 1 ≥ η'𝒜₃/4` once `η'𝒜₃ ≥ 4`
    intro q hq
    have hqa : max qA 4 ≤ q := (le_max_left _ _).trans hq
    have hqg : qG ≤ q := (le_max_right _ _).trans hq
    have hbig : 4 / (η' : ℝ) ≤ A3 q := hqG q hqg
    have hηr : (0 : ℝ) < η' := by exact_mod_cast hη'0
    have hηA : 4 ≤ (η' : ℝ) * A3 q := by
      have := mul_le_mul_of_nonneg_left hbig hηr.le
      rwa [mul_div_cancel₀ _ hηr.ne'] at this
    have hlo := (NearCubicGates.Close.Closure.budgetOf_bounds η' hη'0 q (hqA4 q hqa).1).2
    show (η' : ℝ) / 4 * A3 q ≤ (NearCubicGates.Close.Closure.budgetOf η' q : ℝ)
    nlinarith
  · -- littleO
    obtain ⟨on, hsplit⟩ := W.split
    exact gate_littleO s g _ W.A W.B W.a W.sigma W.hot W.ha W.hsigma
      ⟨on, fun N hN => by
        obtain ⟨h1, h2⟩ := hsplit N hN
        exact ⟨by rw [Weak.runtime_eq]; exact h1, h2⟩⟩
  · -- one-sided (`lem:ae-machine` (iii))
    exact Weak.one_sided W.worker W.htapes W.result W.fuel _
      (Weak.allInputRun_of_total W.worker W.htapes W.result W.fuel W.total)
      (fun n x => (s.hierarchy (fun n => n ^ (g.k + 2)) g.clock).hierarchy.timedView.accepts n x = true)
      (fun n x bits h => by
        obtain ⟨G, hG⟩ := W.sound n x bits h
        exact meaning_sound ctr wb (εT : ℝ) ω n x G hG)

end NearQuarticWires.Transfer
