import SourceAdapters.Assembly.Field6Ordinary

/-!
# Input 6 from BCGT13 Theorem 11.1 at the tuple `(2, 4, 0, 1)`

The release assumes the repaired proof bound for BCGT13 Theorem 11.1 only at `(η, κ0, γ, μ) = (2, 4, 0, 1)`
(`NearCubicGates.Published.BCGT13.BCGT13_Theorem11_1_Fixed`, `Statement.lean`). This module builds the short PCP of
input 6 from that statement (`field6OrdinaryFixed`), following `Field6Ordinary.lean` with the tuple fixed, and proves
that the printed full theorem implies this weaker fixed bound (`bcgt13Fixed_of_theorem11_1`).
The repaired term is `16·κ^{log₂ c}`, from Lemma 11.10 and Corollary 11.13 (ECCC rev. 3, pp.67–68).
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option warningAsError true
noncomputable section
namespace NearCubicGates.Adapters.Assembly.Fixed
open Finset Polynomial NearCubicWires.WireExponent3_5 NearCubicWires.CanonicalBinary
open NearCubicGates.Published.BCGT13 NearCubicGates.Adapters.ShortPCP
open NearCubicGates.Adapters.ACSP.Affine NearCubicGates.Adapters.Joins NearCubicGates.Adapters.Joins.SingleRun
open NearCubicGates.Adapters.Joins.SingleRun.Amplified NearCubicGates.Adapters.ShortPCP.SmallBias
open NearCubicGates.Adapters.ShortPCP.Verifier

/-- The published input: the repaired BCGT13 proof bound at `(2, 4, 0, 1)` (`Statement.lean`). -/
abbrev FixedLeaf : Prop := BCGT13_Theorem11_1_Fixed

/-- The tuple `(2, 4, 0, 1)` satisfies Eq. (6). -/
theorem fixed_valid : Tuple.fixed.Valid := tuple0_valid

/-- The tuple `(2, 4, 0, 1)` lies in the positive-exponent domain of Theorem 11.1. -/
theorem fixed_positive_exponents : Tuple.fixed.PositiveExponents := tuple0_positive_exponents

/-- The printed full statement implies the weaker repaired fixed-tuple bound. -/
theorem bcgt13Fixed_of_theorem11_1 (h : BCGT13_Theorem11_1) : BCGT13_Theorem11_1_Fixed := by
  intro F _ _ _ _ ℓ hF B O hB
  have hs := h Tuple.fixed fixed_valid fixed_positive_exponents F ℓ hF B O hB
  constructor
  · intro d hd1 hd
    refine ⟨(hs.1 d hd1 hd).1, ?_⟩
    intro p π δ hfar
    have hκ : 1 ≤ B.length := by
      by_contra hn
      have hz : B.length = 0 := by omega
      simp [hz] at hd
      omega
    apply repaired_soundness_of_printed B.length hκ 1 _ δ (by norm_num)
    · have hzero := (hs.1 d hd1 hd).2 p π 0 (by
        intro q hq
        unfold fracDist
        positivity)
      simpa using hzero
    · exact (hs.1 d hd1 hd).2 p π δ hfar
  · intro BH OH hBH hsub d hHd hd
    refine ⟨(hs.2 BH OH hBH hsub d hHd hd).1, ?_⟩
    intro p π δ hfar
    have hκ : 1 ≤ B.length := by
      have hone : 1 ≤ 2 ^ BH.length := Nat.one_le_pow _ _ (by omega)
      by_contra hn
      have hz : B.length = 0 := by omega
      simp [hz] at hd
      omega
    apply repaired_soundness_of_printed B.length hκ 2 _ δ (by norm_num)
    · have hzero := (hs.2 BH OH hBH hsub d hHd hd).2 p π 0 (by
        intro q hq
        unfold fracDist
        positivity)
      simpa using hzero
    · exact (hs.2 BH OH hBH hsub d hHd hd).2 p π δ hfar

section

variable (h : FixedLeaf)
  {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (ℓ : ℕ) (hF : Fintype.card F = 2 ^ ℓ)
  (B : List F) (O : F) (hB : IsBasis B O)

/-- The transcribed `V_RS` (BCGT13 Algorithm 13 / Lemma 12.19) as a `StrongPCPP`, soundness factor
`1/(1 + K_κ)` (Theorem 11.1). -/
noncomputable def rsOfFixed (d : ℕ) (hd1 : 1 ≤ d) (hd : d < 2 ^ B.length) :
    StrongPCPP F (span B O) (RS (span B O) d) (1 / (1 + repairedSoundTerm B.length)) where
  rand := (vRS tuple0 B O d).rand
  length := (vRS tuple0 B O d).length
  accepts := (vRS tuple0 B O d).accepts B O
  complete := ((h F ℓ hF B O hB).1 d hd1 hd).1
  sound := by
    intro p π δ hfar
    have hs := ((h F ℓ hF B O hB).1 d hd1 hd).2 p π δ hfar
    unfold FlatVerifier.acceptProb at hs
    unfold acceptFrac
    rw [one_div_mul_eq_div]
    exact hs

/-- The transcribed `V_VRS` (BCGT13 Algorithm 12 / Lemma 12.20) as a `StrongPCPP`, soundness factor
`1/(2 + K_κ)` (Theorem 11.1). -/
noncomputable def vrsOfFixed (BH : List F) (OH : F) (hBH : IsBasis BH OH) (hsub : span BH OH ⊆ span B O)
    (d : ℕ) (hHd : 2 ^ BH.length ≤ d) (hd : d < 2 ^ B.length) :
    StrongPCPP F (span B O) (VRS (span B O) (span BH OH) d)
      (1 / (2 + repairedSoundTerm B.length)) where
  rand := (vVRS tuple0 B O BH OH d).rand
  length := (vVRS tuple0 B O BH OH d).length
  accepts := (vVRS tuple0 B O BH OH d).accepts B O
  complete := ((h F ℓ hF B O hB).2 BH OH hBH hsub d hHd hd).1
  sound := by
    intro p π δ hfar
    have hs := ((h F ℓ hF B O hB).2 BH OH hBH hsub d hHd hd).2 p π δ hfar
    unfold FlatVerifier.acceptProb at hs
    unfold acceptFrac
    rw [one_div_mul_eq_div]
    exact hs

end

variable {Kc : ℕ} {c : Instance} {xs : List Bool}
theorem singleRun_core_fixed (h11 : FixedLeaf) (hG : SingleRun.Good Kc c xs) :
    (c.Accepts xs → ∃ π : ℕ → Bool, ∀ R : List Bool, SingleRun.accepts c xs π R = true) ∧
    (¬ c.Accepts xs → ∀ π : ℕ → Bool,
      acceptFrac (fun R : Fin (r0 c) → Bool => SingleRun.accepts c xs π (List.ofFn R)) ≤
        1 - 1 / (((144 * max Kc 1 : ℕ) : ℝ) * (c.f : ℝ) ^ 37)) := by
  have hp := Good.modOk hG
  have hirr := Good.irr hG
  haveI : Fact (Irreducible c.irrPoly) := ⟨hirr⟩
  letI : Fintype c.Fld := Fintype.ofEquiv _ (GF.encEquiv c.irr c.f hp)
  letI : DecidableEq c.Fld := Classical.decEq _
  haveI : CharP c.Fld 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) c.Fld).injective 2
  have hcard := card_fld hG
  have hspan := span_mono_univ c hp
  have hB : IsBasis (monoBasis c) 0 := isBasis_mono c hp
  have hBH : IsBasis (c.hBasis.map c.elt) (c.elt c.hOffset) := isBasis_map c _ _ (indep_H hG)
  have hBI : IsBasis (c.iBasis.map c.elt) (c.elt c.iOffset) := isBasis_map c _ _ (indep_I hG)
  have hlenB : (monoBasis c).length = c.f := length_monoBasis c
  have hlenH : (c.hBasis.map c.elt).length = c.mH := List.length_map _
  have hlenI : (c.iBasis.map c.elt).length = c.m := List.length_map _
  have hmH := hG.mH_two_le
  have hmI := hG.m_lt
  have h1m := hG.one_le_m
  have hf2 := Good.two_le_f hG
  have hpowH : 2 ^ c.mH < 2 ^ c.f := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hpowI : 2 ^ c.m < 2 ^ c.mH := Nat.pow_lt_pow_right (by norm_num) hmI
  have hH1 : 2 ≤ 2 ^ c.mH := by
    have : 2 ^ 1 ≤ 2 ^ c.mH := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa using this
  have hdA : 2 ^ c.mH - 1 < 2 ^ (monoBasis c).length := by rw [hlenB]; omega
  have hdA1 : 1 ≤ 2 ^ c.mH - 1 := by omega
  have hHd : 2 ^ (c.hBasis.map c.elt).length ≤ dH c := by rw [hlenH]; exact Good.two_pow_mH_le_dH hG
  have hdH : dH c < 2 ^ (monoBasis c).length := by rw [hlenB]; exact (Good.dH_lt hG).1
  have hId : 2 ^ (c.iBasis.map c.elt).length ≤ 2 ^ c.mH - 1 := by rw [hlenI]; omega
  have hsub : ∀ S : Finset c.Fld, S ⊆ span (monoBasis c) 0 := fun S => hspan ▸ Finset.subset_univ S
  have hbij : Function.Bijective (fun b : Fin c.f → Bool => getRandElt (monoBasis c) 0 (List.ofFn b)) := by
    have := elt_maskOfBits_bijective c hp
    convert this using 1
    funext b
    exact getRandElt_mono c b
  let D := (request c xs [[]]).acsp (RingHom.id c.Fld)
  let K : ℝ := repairedSoundTerm (monoBasis c).length
  let W : SubVerifiers D (1 / (1 + K)) (1 / (2 + K)) (1 / (2 + K)) :=
    { f := c.f
      elem := Equiv.ofBijective _ hbij
      VR := strongCongr hspan (by rw [hspan]; try rfl)
        (rsOfFixed h11 c.f hcard (monoBasis c) 0 hB (2 ^ c.mH - 1) hdA1 hdA)
      VH := strongCongr hspan (by rw [hspan]; try rfl)
        (vrsOfFixed h11 c.f hcard (monoBasis c) 0 hB (c.hBasis.map c.elt) (c.elt c.hOffset)
          hBH (hsub _) (dH c) hHd hdH)
      VI := strongCongr hspan (by rw [hspan]; try rfl)
        (vrsOfFixed h11 c.f hcard (monoBasis c) 0 hB (c.iBasis.map c.elt) (c.elt c.iOffset)
          hBI (hsub _) (2 ^ c.mH - 1) hId hdA) }
  have hR : W.VR.rand ≤ r0 c := by
    show (vRS tuple0 (monoBasis c) 0 (2 ^ c.mH - 1)).rand ≤ r0 c
    rw [vRS_rand_eq, hlenB]; unfold r0; omega
  have hH : W.VH.rand ≤ r0 c := by
    show (vVRS tuple0 (monoBasis c) 0 (c.hBasis.map c.elt) (c.elt c.hOffset) (dH c)).rand ≤ r0 c
    rw [vVRS_rand_eq, hlenB, hlenH]; unfold r0; omega
  have hf : W.f ≤ r0 c := by show c.f ≤ r0 c; unfold r0; omega
  have hI : W.VI.rand ≤ r0 c := by
    show (vVRS tuple0 (monoBasis c) 0 (c.iBasis.map c.elt) (c.elt c.iOffset) (2 ^ c.mH - 1)).rand ≤ r0 c
    rw [vVRS_rand_eq, hlenB, hlenI]; unfold r0; omega
  let dec : (ℕ → Bool) → ProofTable W := fun π =>
    { p0 := ((request c xs [[]]).decode (RingHom.id c.Fld) π).p0
      π0 := ((request c xs [[]]).decode (RingHom.id c.Fld) π).π0
      p1 := ((request c xs [[]]).decode (RingHom.id c.Fld) π).p1
      π1 := ((request c xs [[]]).decode (RingHom.id c.Fld) π).π1
      πc := ((request c xs [[]]).decode (RingHom.id c.Fld) π).πc }
  have hpt : ∀ ρ : ℕ → Bool, (request c xs [[]]).consistPoint (RingHom.id c.Fld) ρ =
      W.elem (pre W.f hf fun i : Fin (r0 c) => ρ i.val) := by
    intro ρ
    show c.elt (bitsValue ((List.range c.f).map ρ)) =
      getRandElt (monoBasis c) 0 (List.ofFn fun i : Fin c.f => ρ i.val)
    rw [getRandElt_mono, bitsValue_range_map]
  have hacc : ∀ (π : ℕ → Bool) (ρ : ℕ → Bool),
      (request c xs [[]]).runVerdict (RingHom.id c.Fld) ((request c xs [[]]).decode (RingHom.id c.Fld) π) ρ =
        W.acceptsAt (r0 c) hR hH hf hI (dec π) (fun i => ρ i.val) := by
    intro π ρ
    unfold Request.runVerdict SubVerifiers.acceptsAt
    rw [hpt]
    rfl
  have hnot : ¬ c.Accepts xs → ¬ D.Mem := fun h hm => h ((mem_iff_accepts hG [[]]).mp hm)
  refine ⟨?_, ?_⟩
  · -- completeness: encode the complete table of `completeAt` in bits
    intro ha
    obtain ⟨pf, hpf⟩ := W.completeAt (good_instance hG [[]]) ((mem_iff_accepts hG [[]]).mpr ha)
    let L0 := W.VR.length
    let L1 := W.VH.length
    let LC := W.VI.length
    let target : ℕ → c.Fld := fun k =>
      if k < 2 ^ c.f then pf.p0 (c.elt k)
      else if h1 : k - 2 ^ c.f < L0 then pf.π0 ⟨k - 2 ^ c.f, h1⟩
      else if k - 2 ^ c.f - L0 < 2 ^ c.f then pf.p1 (c.elt (k - 2 ^ c.f - L0))
      else if h3 : k - 2 ^ c.f - L0 - 2 ^ c.f < L1 then pf.π1 ⟨k - 2 ^ c.f - L0 - 2 ^ c.f, h3⟩
      else if h4 : k - 2 ^ c.f - L0 - 2 ^ c.f - L1 < LC then pf.πc ⟨k - 2 ^ c.f - L0 - 2 ^ c.f - L1, h4⟩
      else 0
    let w : ℕ → ℕ := fun k => (request c xs [[]]).wordOf (RingHom.id c.Fld) (target k)
    let π : ℕ → Bool := fun a => (w (a / c.f)).testBit (a % c.f)
    have hf0 : 0 < c.f := by omega
    have hword : ∀ k, (request c xs [[]]).wordAt π k = w k := by
      intro k
      unfold Request.wordAt
      rw [bitsValue_range_map]
      have hb : (fun j : Fin (request c xs [[]]).code.f => π (k * (request c xs [[]]).code.f + j.val)) =
          bitsOf c.f (w k) := by
        funext j
        have hj : j.val < c.f := j.isLt
        have h1 : (k * c.f + j.val) / c.f = k := by
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ hf0, Nat.div_eq_of_lt hj, zero_add]
        have h2 : (k * c.f + j.val) % c.f = j.val := by
          rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
        simp only [π, bitsOf]
        show (w ((k * c.f + j.val) / c.f)).testBit ((k * c.f + j.val) % c.f) = _
        rw [h1, h2]
      rw [hb]
      exact maskOfBits_bitsOf c.f _ (wordOf_lt c xs [[]] _)
    have helt : ∀ k, (request c xs [[]]).elt (RingHom.id c.Fld) ((request c xs [[]]).wordAt π k) = target k := by
      intro k
      rw [hword]
      exact elt_wordOf c xs [[]] hp _
    have hwo : ∀ a : c.Fld, (request c xs [[]]).wordOf (RingHom.id c.Fld) a < 2 ^ c.f := wordOf_lt c xs [[]]
    have hew : ∀ a : c.Fld, c.elt ((request c xs [[]]).wordOf (RingHom.id c.Fld) a) = a := elt_wordOf c xs [[]] hp
    have hL0 : L0 = ((request c xs [[]]).vR (RingHom.id c.Fld)).length := rfl
    have hL1 : L1 = ((request c xs [[]]).vH (RingHom.id c.Fld)).length := rfl
    have hLC : LC = ((request c xs [[]]).vI (RingHom.id c.Fld)).length := rfl
    have hdec : dec π = pf := by
      obtain ⟨p0, π0, p1, π1, πc⟩ := pf
      simp only [dec]
      congr 1
      · funext α
        have h0 := hwo α
        show (request c xs [[]]).elt (RingHom.id c.Fld)
          ((request c xs [[]]).wordAt π ((request c xs [[]]).wordOf (RingHom.id c.Fld) α)) = p0 α
        rw [helt]
        simp only [target]
        split_ifs
        · exact congrArg p0 (hew α)
      · funext t
        have ht := t.isLt
        show (request c xs [[]]).elt (RingHom.id c.Fld) ((request c xs [[]]).wordAt π (2 ^ c.f + t.val)) = π0 t
        rw [helt]
        simp only [target]
        split_ifs <;> first | (exfalso; omega) | (congr 1; ext; simp only; omega)
      · funext α
        have h0 := hwo α
        show (request c xs [[]]).elt (RingHom.id c.Fld) ((request c xs [[]]).wordAt π
          (2 ^ c.f + L0 + (request c xs [[]]).wordOf (RingHom.id c.Fld) α)) = p1 α
        rw [helt]
        simp only [target]
        split_ifs <;> first | (exfalso; omega) | skip
        rw [show 2 ^ c.f + L0 + (request c xs [[]]).wordOf (RingHom.id c.Fld) α - 2 ^ c.f - L0 =
          (request c xs [[]]).wordOf (RingHom.id c.Fld) α by omega]
        exact congrArg p1 (hew α)
      · funext t
        have ht := t.isLt
        show (request c xs [[]]).elt (RingHom.id c.Fld) ((request c xs [[]]).wordAt π
          (2 * 2 ^ c.f + L0 + t.val)) = π1 t
        rw [helt]
        simp only [target]
        split_ifs <;> first | (exfalso; omega) | (congr 1; ext; simp only; omega)
      · funext t
        have ht := t.isLt
        show (request c xs [[]]).elt (RingHom.id c.Fld) ((request c xs [[]]).wordAt π
          (2 * 2 ^ c.f + L0 + L1 + t.val)) = πc t
        rw [helt]
        simp only [target]
        split_ifs <;> first | (exfalso; omega) | (congr 1; ext; simp only; omega)
    refine ⟨π, fun R => ?_⟩
    rw [accepts_eq hG, hacc, hdec]
    exact hpf _ _ _ _ _ _
  · -- soundness
    intro hna π
    have hfun : (fun R : Fin (r0 c) → Bool => SingleRun.accepts c xs π (List.ofFn R)) =
        W.acceptsAt (r0 c) hR hH hf hI (dec π) := by
      funext R
      rw [accepts_eq hG, hacc]
      congr 1
      funext i
      exact getD_ofFn R i
    rw [hfun]
    refine (W.soundAt (r0 c) hR hH hf hI (good_instance hG [[]]) (hnot hna) (dec π)).trans ?_
    have hu := uniform_rejection c.f D.cN (max Kc 1) (by omega) (Good.cN_pos hG) (le_max_right _ _)
      (hG.cN_le.trans (Nat.mul_le_mul_right _ (le_max_left _ _)))
    have hK : K = repairedSoundTerm c.f := by
      show repairedSoundTerm (monoBasis c).length = _
      rw [hlenB]
    rw [hK]
    linarith

theorem amplifiedVerifier_fixed (h11 : FixedLeaf) : AmplifiedVerifier := by
  intro Kc
  refine ⟨144 * max Kc 1, 37, 64, 4, by omega, fun c xs n hG hn => ?_⟩
  obtain ⟨hc, hs⟩ := singleRun_core_fixed h11 hG
  obtain ⟨h1, h2, -, h4, h5⟩ := singleRun_resources hG
  have hN2 : 2 ≤ target c n (144 * max Kc 1) 37 := by
    have e1 : 1 ≤ r0 c ^ 2 := Nat.one_le_pow _ _ (by omega)
    have e2 : 1 ≤ c.f ^ 37 := Nat.one_le_pow _ _ (by omega)
    unfold target
    have : 2 ≤ r0 c ^ 2 * n := by nlinarith
    have : 2 ≤ r0 c ^ 2 * n * (144 * max Kc 1) := le_trans this (Nat.le_mul_of_pos_right _ (by omega))
    exact le_trans this (Nat.le_mul_of_pos_right _ (by omega))
  refine ⟨?_, ?_, masks_length c n _ _ hN2, masks_mem_length c n _ _, ?_, ?_, h1, h2, h4, h5⟩
  · intro ha
    obtain ⟨π, hπ⟩ := hc ha
    refine ⟨π, fun R => ?_⟩
    rw [amplified_all hG]
    simp [hπ]
  · intro hna π
    exact amplified_sound hG n _ 37 (by omega) hn h1 (by omega) π (hs hna π)
  · intro π R R' hR
    rw [amplified_all hG, amplified_all hG]
    congr 1
    funext σ
    congr 2
    funext i
    simp only [Request.maskedCoins, hR i.val i.isLt]
  · intro π π' hπ R
    rw [amplified_all hG, amplified_all hG]
    congr 1
    funext σ
    exact accepts_local hG π π' hπ _


/-- **Input 6 from the fixed-tuple input**: the short PCP as an oracle circuit (`OrdinaryOracleCircuitPCP`) from
BCGT13 Theorem 11.1 at `(2, 4, 0, 1)` and the irreducible-polynomial algorithm. -/
theorem field6OrdinaryFixed (h11 : FixedLeaf)
    (hIrr : NearCubicGates.Published.Shoup.FindIrrPolyAlgorithm17) :
    NearCubicGates.Adapters.Assembly.OrdinaryOracleCircuitPCP :=
  NearCubicGates.Adapters.ShortPCP.OracleCircuitPCP.shortPCP_ordinary_of_joins
    (NearCubicGates.Adapters.Assembly.ownReduction hIrr) (amplifiedVerifier_fixed h11)
    NearCubicGates.Adapters.ShortPCP.Time.singleRunTime
    NearCubicGates.Adapters.Compile.OraclePrint.computationToCircuit
    NearCubicGates.Adapters.ShortPCP.MaskMachine.maskMachine
    NearCubicGates.Adapters.ShortPCP.OracleCircuitPCP.assemblyMachine

end NearCubicGates.Adapters.Assembly.Fixed
