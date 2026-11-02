import Proof.Quartic.Worker.Worker.Complete
import Proof.Foundations.SupplierPipeline
import Proof.Gates.Transfer.CaseOne

/-!
# Completeness of the weak machine for the wire measure (`lem:ae-table` and `lem:ae-estimate` (iii))

Let `C` be a `SYM∘THR` circuit on the hard table's `q + cl + pl` inputs with at most `b ≤ q⁴` wires. The guess of
`lem:ae-table` takes, for every auxiliary name, a minimizing address cofactor of `C` (`lem:ae-wires` (b)) and
normalizes it gate by gate on the gate's own inputs (`lem:ae-wires` (d), `normalizeGatePreservingSupport` imported
from `Proof.Foundations.SupplierPipeline`). The resulting normalized circuits have unit top coefficients and at most
`W(C) ≤ b` wires (`cofCircuit_good4`); in particular their top weight is at most `b`, which is the size limit
`Guess.SizeOK` of the weak machine. Every call is normalized with total wire count at most `2b`
(`Guess.callOf_admitted4`), and the counter's completeness under `2b ≤ a ω 𝒜₄(q)` supplies witnesses of radius `ω`
for every term (`useful_exists4`). Then `𝒰 ≤ (5 + ε) δ + 10 ω < γ − ε` (`approx_complete4`).

Adapted from `Proof.Gates.Worker.Complete` of the near-cubic gate proof, with the wire measure and the cap 𝒜₄; the
choice of cofactors and the penalty bound are those of `Proof.Quartic.Worker.Worker.Complete`, applied to `C` viewed
as a weighted circuit with unit coefficients (`ofSymmetric`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Worker4.Worker
open NearCubicGates NearCubicGates.Close NearCubicGates.Close.Worker NearQuarticWires.Transfer

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairOrdinary
open NearCubicWires.Bindings.CLW20Lemma311 NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close.Interfaces NearCubicGates NearCubicGates.FiniteAverages
open NearCubicGates.FreshHelperTable NearCubicGates.GadgetTableTransfer NearCubicGates.FiveCycle
open NearCubicGates.CircuitNormalization NearCubicGates.Close NearCubicGates.Close.Worker
open NearCubicWires.SupplierPipeline

/-! ## `SYM∘THR` circuits as weighted circuits with unit coefficients -/

/-- A `SYM∘THR` circuit as a weighted circuit: every coefficient `1`, lookup `g` on the count. -/
noncomputable def ofSymmetric {n : ℕ} (C : SymmetricThresholdCircuit n) : Target.WeightedSymmetricCircuit n where
  bottomCount := C.bottomCount
  bottom := C.bottom
  coefficient := fun _ => 1
  coefficient_ne_zero := fun _ => one_ne_zero
  lookup := fun z => C.top z.toNat

theorem ofSymmetric_eval {n : ℕ} (C : SymmetricThresholdCircuit n) (x : BitInput n) :
    (ofSymmetric C).eval x = C.eval x := by
  classical
  unfold Target.WeightedSymmetricCircuit.eval Target.WeightedSymmetricCircuit.score SymmetricThresholdCircuit.eval
  simp only [ofSymmetric, one_mul]
  congr 1
  have h := Finset.natCast_card_filter (R := ℤ) (fun i => (C.bottom i).eval x = true) Finset.univ
  rw [← Int.toNat_natCast (Finset.univ.filter fun i => (C.bottom i).eval x = true).card, h]
  congr 1

theorem ofSymmetric_eval_fun {n : ℕ} (C : SymmetricThresholdCircuit n) : (ofSymmetric C).eval = C.eval :=
  funext (ofSymmetric_eval C)

/-- The wire count of the bottom gates of a weighted circuit, one top wire per gate. -/
def gateWires {n : ℕ} (C : Target.WeightedSymmetricCircuit n) : ℕ := ∑ i, ((C.bottom i).support.card + 1)

theorem gateWires_ofSymmetric {n : ℕ} (C : SymmetricThresholdCircuit n) :
    gateWires (ofSymmetric C) = C.wireCount := rfl

theorem restrictGate_support_card_le {n k : ℕ} (g : RealThresholdGate (n + k)) (suffix : BitInput k) :
    (Target.restrictGate g suffix).support.card ≤ g.support.card := by
  classical
  have hsub : (Target.restrictGate g suffix).support.image (Fin.castAdd k) ⊆ g.support := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    have : g.weight (Fin.castAdd k j) ≠ 0 := by simpa [Target.restrictGate] using hj
    exact (g.mem_support_iff _).2 this
  calc (Target.restrictGate g suffix).support.card
      = ((Target.restrictGate g suffix).support.image (Fin.castAdd k)).card :=
        (Finset.card_image_of_injective _ (Fin.castAdd_injective n k)).symm
    _ ≤ g.support.card := Finset.card_le_card hsub

theorem gateWires_restrictSuffix_le {n k : ℕ} (C : Target.WeightedSymmetricCircuit (n + k)) (suffix : BitInput k) :
    gateWires (C.restrictSuffix suffix) ≤ gateWires C := by
  unfold gateWires
  exact Finset.sum_le_sum fun i _ => Nat.add_le_add_right (restrictGate_support_card_le (C.bottom i) suffix) 1

/-- `lem:ae-wires` (b): an address cofactor has no more wires. -/
theorem gateWires_addressCofactor_le {n cl pl : ℕ} (C : Target.WeightedSymmetricCircuit (n + cl + pl))
    (aj : Fin (2 ^ cl) × Fin (2 ^ pl)) : gateWires (addressCofactor C aj) ≤ gateWires C :=
  (gateWires_restrictSuffix_le _ _).trans (gateWires_restrictSuffix_le _ _)

/-! ## Normalization on each gate's own inputs (`lem:ae-wires` (d)) -/

theorem supportedDescription_exists (pub : ThresholdNormalizationContract) {n : ℕ} (hn : 1 ≤ n)
    (C : Target.WeightedSymmetricCircuit n) :
    ∃ D : IntegerDescription C, ∀ i j, j ∉ (C.bottom i).support → (D.bottom i).weight j = 0 := by
  classical
  choose T hT using fun i => normalizeGatePreservingSupport pub (C.bottom i)
  have hb := magnitude_fits_parameters hn
  refine ⟨⟨fun i => ⟨(T i).gate.weight, (T i).gate.threshold⟩, fun i x => ?_, fun i => ?_, fun i j => ?_⟩, ?_⟩
  · exact (hT i).1 x
  · exact lt_of_le_of_lt (hT i).2.2.2 hb
  · exact lt_of_le_of_lt ((hT i).2.2.1 j) hb
  · intro i j hj
    exact (T i).zeroOutside j (by rw [(hT i).2.1]; exact hj)

/-- A support-preserving integer description of a weighted circuit. -/
noncomputable def supportedDescription (pub : ThresholdNormalizationContract) {n : ℕ} (hn : 1 ≤ n)
    (C : Target.WeightedSymmetricCircuit n) : IntegerDescription C :=
  Classical.choose (supportedDescription_exists pub hn C)

theorem supportedDescription_zero (pub : ThresholdNormalizationContract) {n : ℕ} (hn : 1 ≤ n)
    (C : Target.WeightedSymmetricCircuit n) :
    ∀ i j, j ∉ (C.bottom i).support → ((supportedDescription pub hn C).bottom i).weight j = 0 :=
  Classical.choose_spec (supportedDescription_exists pub hn C)

theorem wires_toNCircuit_le {n : ℕ} (C : Target.WeightedSymmetricCircuit n) (D : IntegerDescription C)
    (hD : ∀ i j, j ∉ (C.bottom i).support → (D.bottom i).weight j = 0) :
    wires (toNCircuit C D) ≤ gateWires C := by
  classical
  unfold wires toNCircuit gateWires
  rw [List.map_ofFn, List.sum_ofFn]
  refine Finset.sum_le_sum fun i _ => Nat.add_le_add_right ?_ 1
  unfold fanIn
  refine Finset.card_le_card fun j hj => ?_
  by_contra hns
  exact (Finset.mem_filter.mp hj).2 (hD i j hns)

theorem toNCircuit_unitTop {n : ℕ} (C : Target.WeightedSymmetricCircuit n) (D : IntegerDescription C)
    (h1 : ∀ i, C.coefficient i = 1) : UnitTop (toNCircuit C D) := by
  intro a ha
  simp only [toNCircuit, List.mem_ofFn] at ha
  obtain ⟨i, rfl⟩ := ha
  exact h1 i

@[simp] theorem wires_empty (n : ℕ) : wires (NCircuit.empty n) = 0 := rfl

/-- With unit top coefficients, the top weight is the number of occurrences, at most the wire count. -/
theorem topWeight_le_wires {n B : ℕ} {C : NCircuit n} (hw : C.WellFormed B) (hu : UnitTop C) :
    C.topWeight ≤ wires C := by
  have h1 : (C.coeffs.map Int.natAbs).sum = C.coeffs.length := by
    have : C.coeffs.map Int.natAbs = List.replicate C.coeffs.length 1 :=
      List.eq_replicate_iff.2 ⟨by simp, fun b hb => by
        obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hb
        rw [hu a ha]; rfl⟩
    rw [this, List.sum_replicate, smul_eq_mul, mul_one]
  have h2 : ∀ gs : List (NormalizedThresholdGate n), gs.length ≤ (gs.map fun g => fanIn g + 1).sum := by
    intro gs
    induction gs with
    | nil => simp
    | cons g gs ih => simp only [List.length_cons, List.map_cons, List.sum_cons]; omega
  unfold NCircuit.topWeight
  rw [h1, ← hw.1]
  exact h2 C.gates

/-! ## Calls of a guess of normalized circuits -/

namespace Guess
variable {s : GateSources} {g : GateParams} (P : ThreeQueryPCPP) {N : ℕ} (x : BitInput N)
  (G : Guess (width s g N))

/-- Every call of a term is a normalized call (§3.1) with total wire count at most `2b`, when every guessed circuit
is normalized, has unit top coefficients and at most `b ≤ q⁴` wires (`lem:ae-estimate` (i)). -/
theorem callOf_admitted4 {B1 B2 : ℕ} (ω : ℚ) (b : ℕ) (ops : List (Bool × Atom)) (c : Call)
    (hc : G.callOf P x ω ops = some c)
    (hwf : ∀ o ∈ ops, ∀ j, o.2 = .aux j →
      (G.circuits j).WellFormed (Call.B0 (width s g N)) ∧ UnitTop (G.circuits j) ∧ wires (G.circuits j) ≤ b)
    (hq4 : 4 ≤ width s g N) (hb : b ≤ width s g N ^ 4) (hr1 : 1 ≤ ω * (width s g N : ℚ) ^ B1)
    (hr2 : ω ≤ 1 / 16) (hr3 : (ratWord ω).length ≤ width s g N ^ B2) :
    Admitted4 B1 B2 c ∧ callWires c ≤ 2 * b := by
  classical
  have hwf' : ∀ e ∈ ops.map Prod.snd, ∀ j, e = .aux j →
      (G.circuits j).WellFormed (Call.B0 (width s g N)) ∧ UnitTop (G.circuits j) ∧ wires (G.circuits j) ≤ b := by
    intro e he j hj
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 he
    exact hwf o ho j hj
  unfold Guess.callOf at hc
  generalize ops.map Prod.snd = as at hc hwf'
  have hE := empty_wellFormed (width s g N) (Call.B0 (width s g N))
  have hEu : UnitTop (NCircuit.empty (width s g N)) := fun a ha => by simp [NCircuit.empty] at ha
  have hb2 : b ≤ 2 * width s g N ^ 4 := by omega
  -- the single / parity call on circuit `j` with support `S`
  have hsingle : ∀ (j : ℕ) (S : Finset (Fin (width s g N))),
      (G.circuits j).WellFormed (Call.B0 (width s g N)) ∧ UnitTop (G.circuits j) ∧ wires (G.circuits j) ≤ b →
      Admitted4 B1 B2 (G.singleCall ω j S) ∧ callWires (G.singleCall ω j S) ≤ 2 * b := by
    intro j S ⟨hw, hu, ht⟩
    by_cases hS : S.Nonempty
    · rw [G.singleCall_pos ω j S hS]
      refine ⟨⟨hq4, hw, hE, hu, hEu, fun _ => rfl, fun h => absurd rfl h, ?_, ?_, hr1, hr2, hr3,
        by simp only [List.length_map, canonList]; exact (List.length_filter_le _ _).trans (by simp)⟩, ?_⟩
      · intro i hi
        obtain ⟨k, -, rfl⟩ := List.mem_map.1 hi
        exact k.isLt
      · show wires (G.circuits j) + wires (NCircuit.empty _) ≤ 2 * width s g N ^ 4
        rw [wires_empty]; omega
      · show wires (G.circuits j) + wires (NCircuit.empty _) ≤ 2 * b
        rw [wires_empty]; omega
    · rw [G.singleCall_neg ω j S hS]
      refine ⟨⟨hq4, hw, hE, hu, hEu, fun _ => rfl, fun _ => rfl, by simp, ?_, hr1, hr2, hr3, by simp⟩, ?_⟩
      · show wires (G.circuits j) + wires (NCircuit.empty _) ≤ 2 * width s g N ^ 4
        rw [wires_empty]; omega
      · show wires (G.circuits j) + wires (NCircuit.empty _) ≤ 2 * b
        rw [wires_empty]; omega
  rcases as with _ | ⟨a₁, _ | ⟨a₂, _ | ⟨a₃, rest⟩⟩⟩
  · simp at hc
  · cases a₁ with
    | sys u => simp at hc
    | aux j =>
      simp only [Option.some.injEq] at hc
      subst hc
      exact hsingle j ∅ (hwf' _ (by simp) j rfl)
  · cases a₁ with
    | sys u =>
      cases a₂ with
      | sys v => simp at hc
      | aux j =>
        simp only [Option.some.injEq] at hc
        subst hc
        exact hsingle j _ (hwf' _ (by simp) j rfl)
    | aux i =>
      cases a₂ with
      | sys u =>
        simp only [Option.some.injEq] at hc
        subst hc
        exact hsingle i _ (hwf' _ (by simp) i rfl)
      | aux j =>
        dsimp only at hc
        by_cases hij : i = j
        · rw [if_pos hij] at hc; simp at hc
        · rw [if_neg hij] at hc
          simp only [Option.some.injEq] at hc
          subst hc
          obtain ⟨hwi, hui, hti⟩ := hwf' _ (by simp) i rfl
          obtain ⟨hwj, huj, htj⟩ := hwf' _ (by simp) j rfl
          refine ⟨⟨hq4, hwi, hwj, hui, huj, fun h => absurd rfl h, fun _ => rfl, by simp [Guess.pairCall], ?_, hr1, hr2,
            hr3, by simp [Guess.pairCall]⟩, ?_⟩
          · show wires (G.circuits i) + wires (G.circuits j) ≤ 2 * width s g N ^ 4
            omega
          · show wires (G.circuits i) + wires (G.circuits j) ≤ 2 * b
            omega
  · cases a₁ <;> cases a₂ <;> simp at hc


end Guess


section Construct
variable (s : GateSources) (P : ThreeQueryPCPP) (g : GateParams) {N : ℕ} (x : BitInput N)
  (B : Outer.OuterGuess (width s g N)) (hD : ∀ r, (substituted s g x B).D.eval r = true)
  (C : SymmetricThresholdCircuit
    ((substituted s g x B).n + clauseWidth g.clauseDegree (width s g N) + g.positionLog))
  (pub : ThresholdNormalizationContract) (hn : 1 ≤ width s g N)

/-- The normalized address cofactor chosen for a name: the cofactor of `lem:ae-table`, normalized gate by gate on its
own inputs (`lem:ae-wires` (d)). -/
noncomputable def cofCircuit4
    (nm : Name P (substituted s g x B) ⊕ Fin (2 ^ clauseWidth g.clauseDegree (width s g N))) :
    NCircuit (width s g N) :=
  toNCircuit (addressCofactor (ofSymmetric C) (chosenAddrOf P (substituted s g x B) hD _ _ (ofSymmetric C) nm))
    (supportedDescription pub hn _)

/-- One circuit per auxiliary name: proof coordinate `j`, then helper `proofBits + a`. -/
noncomputable def proofCircuits4 (j : ℕ) : NCircuit (width s g N) :=
  if h : j < (pcpp s P g x B).proofBits then
    cofCircuit4 s P g x B hD C pub hn (Sum.inl (Fin.natAdd (sysCount s P g x B) ⟨j, h⟩))
  else if h' : j - (pcpp s P g x B).proofBits < 2 ^ clauseWidth g.clauseDegree (width s g N) then
    cofCircuit4 s P g x B hD C pub hn (Sum.inr ⟨j - (pcpp s P g x B).proofBits, h'⟩)
  else NCircuit.empty _

/-- The guess with the pair `B`, the chosen circuits, and witness prefixes `W`. -/
noncomputable abbrev baseGuess4 (W : ℕ → Fin 10 → List Bool) : Guess (width s g N) :=
  ⟨B, proofCircuits4 s P g x B hD C pub hn, W⟩

theorem cofCircuit_eval4 (nm : Name P (substituted s g x B) ⊕ Fin (2 ^ clauseWidth g.clauseDegree (width s g N)))
    (r : BitInput (width s g N)) :
    (cofCircuit4 s P g x B hD C pub hn nm).eval r =
      (addressCofactor (ofSymmetric C) (chosenAddrOf P (substituted s g x B) hD _ _ (ofSymmetric C) nm)).eval r :=
  toNCircuit_eval _ _ r

theorem cofCircuit_good4 (nm : Name P (substituted s g x B) ⊕ Fin (2 ^ clauseWidth g.clauseDegree (width s g N))) :
    (cofCircuit4 s P g x B hD C pub hn nm).WellFormed (Call.B0 (width s g N)) ∧
      UnitTop (cofCircuit4 s P g x B hD C pub hn nm) ∧ wires (cofCircuit4 s P g x B hD C pub hn nm) ≤ C.wireCount :=
  ⟨toNCircuit_wellFormed _ _, toNCircuit_unitTop _ _ (fun _ => rfl),
    (wires_toNCircuit_le _ _ (supportedDescription_zero pub hn _)).trans
      ((gateWires_addressCofactor_le _ _).trans (le_of_eq (gateWires_ofSymmetric C)))⟩

theorem proofCircuits_good4 (W : ℕ → Fin 10 → List Bool) (j : ℕ)
    (hj : j < (baseGuess4 s P g x B hD C pub hn W).auxCount P x) :
    (proofCircuits4 s P g x B hD C pub hn j).WellFormed (Call.B0 (width s g N)) ∧
      UnitTop (proofCircuits4 s P g x B hD C pub hn j) ∧ wires (proofCircuits4 s P g x B hD C pub hn j) ≤ C.wireCount := by
  unfold proofCircuits4
  split_ifs with h h'
  · exact cofCircuit_good4 s P g x B hD C pub hn _
  · exact cofCircuit_good4 s P g x B hD C pub hn _
  · exfalso
    unfold Guess.auxCount gadgets baseGuess4 at hj
    exact h' (by simp only at hj; omega)

theorem assignment_eq4 (W : ℕ → Fin 10 → List Bool) (r : BitInput (width s g N))
    (X : Name P (substituted s g x B)) :
    (baseGuess4 s P g x B hD C pub hn W).assignment P x r X =
      chosenOf P (substituted s g x B) hD _ _ (ofSymmetric C) (Sum.inl X) r := by
  have hsc : sysCount s P g x B = (checkedCircuit P.code (substituted s g x B)).n := rfl
  by_cases hX : X.val < (checkedCircuit P.code (substituted s g x B)).n
  · calc (baseGuess4 s P g x B hD C pub hn W).assignment P x r X
          = sysEnc P.code (substituted s g x B).n r ⟨X.val, hX⟩ :=
            Guess.assignment_lt P x (baseGuess4 s P g x B hD C pub hn W) r X hX
      _ = originalOf P (substituted s g x B) hD X r := (originalOf_lt P _ hD X hX r).symm
      _ = chosenOf P (substituted s g x B) hD _ _ (ofSymmetric C) (Sum.inl X) r := by
            rw [chosenOf_sys _ _ _ _ _ _ _ hX]
  · have hge : sysCount s P g x B ≤ X.val := by rw [hsc]; exact Nat.le_of_not_lt hX
    have hlt : X.val - sysCount s P g x B < (pcpp s P g x B).proofBits := by
      have := X.isLt
      have hpb : (pcpp s P g x B).proofBits = (P.output (checkedCircuit P.code (substituted s g x B))).proofBits := rfl
      omega
    have hX' : (Fin.natAdd (sysCount s P g x B) ⟨X.val - sysCount s P g x B, hlt⟩ :
        Fin (sysCount s P g x B + (pcpp s P g x B).proofBits)) = X := by
      ext; simp only [Fin.val_natAdd]; omega
    calc (baseGuess4 s P g x B hD C pub hn W).assignment P x r X
          = (proofCircuits4 s P g x B hD C pub hn (X.val - sysCount s P g x B)).eval r :=
            Guess.assignment_ge P x (baseGuess4 s P g x B hD C pub hn W) r X hge
      _ = (cofCircuit4 s P g x B hD C pub hn (Sum.inl X)).eval r := by
            unfold proofCircuits4
            rw [dif_pos hlt]
            exact congrArg (fun nm => (cofCircuit4 s P g x B hD C pub hn (Sum.inl nm)).eval r) hX'
      _ = (addressCofactor (ofSymmetric C) (chosenAddrOf P (substituted s g x B) hD _ _ (ofSymmetric C) (Sum.inl X))).eval r :=
            cofCircuit_eval4 s P g x B hD C pub hn _ r
      _ = chosenOf P (substituted s g x B) hD _ _ (ofSymmetric C) (Sum.inl X) r :=
            (chosenOf_aux P (substituted s g x B) hD (clauseWidth g.clauseDegree (width s g N)) g.positionLog (ofSymmetric C)
              (Sum.inl X) (by simp only [prescribed, Sum.elim_inl, systematicOf, decide_eq_false_iff_not]; exact hX)
              r).symm

theorem helper_eq4 (W : ℕ → Fin 10 → List Bool) (a : Fin (2 ^ clauseWidth g.clauseDegree (width s g N)))
    (r : BitInput (width s g N)) :
    (baseGuess4 s P g x B hD C pub hn W).atomValue P x r ((baseGuess4 s P g x B hD C pub hn W).helper P x a.val) =
      chosenOf P (substituted s g x B) hD _ _ (ofSymmetric C) (Sum.inr a) r := by
  have h1 : ¬ (pcpp s P g x B).proofBits + a.val < (pcpp s P g x B).proofBits := by omega
  have h2 : (pcpp s P g x B).proofBits + a.val - (pcpp s P g x B).proofBits <
      2 ^ clauseWidth g.clauseDegree (width s g N) := by
    have := a.isLt; omega
  have ha : (⟨(pcpp s P g x B).proofBits + a.val - (pcpp s P g x B).proofBits, h2⟩ :
      Fin (2 ^ clauseWidth g.clauseDegree (width s g N))) = a := by ext; simp
  calc (baseGuess4 s P g x B hD C pub hn W).atomValue P x r ((baseGuess4 s P g x B hD C pub hn W).helper P x a.val)
        = (proofCircuits4 s P g x B hD C pub hn ((pcpp s P g x B).proofBits + a.val)).eval r := rfl
    _ = (cofCircuit4 s P g x B hD C pub hn (Sum.inr a)).eval r := by
          unfold proofCircuits4; rw [dif_neg h1, dif_pos h2, ha]
    _ = (addressCofactor (ofSymmetric C) (chosenAddrOf P (substituted s g x B) hD _ _ (ofSymmetric C) (Sum.inr a))).eval r :=
          cofCircuit_eval4 s P g x B hD C pub hn _ r
    _ = chosenOf P (substituted s g x B) hD _ _ (ofSymmetric C) (Sum.inr a) r :=
          (chosenOf_aux P (substituted s g x B) hD (clauseWidth g.clauseDegree (width s g N)) g.positionLog (ofSymmetric C)
            (Sum.inr a) rfl r).symm

theorem meanPenalty_eq4 (W : ℕ → Fin 10 → List Bool) :
    ((baseGuess4 s P g x B hD C pub hn W).family P x).meanPenalty =
      mean (fun a : Fin (2 ^ clauseWidth g.clauseDegree (width s g N)) =>
        mean (penalty (names (clausesOf P (substituted s g x B) _)) (fun a => (clausesOf P (substituted s g x B) _ a).negative)
          (chosenOf P (substituted s g x B) hD _ g.positionLog (ofSymmetric C)) a)) := by
  unfold GadgetFamily.meanPenalty
  congr 1
  funext a
  congr 1
  funext r
  have hx : ∀ i : Fin 3, ((baseGuess4 s P g x B hD C pub hn W).family P x).x a i r =
      literal ((clausesOf P (substituted s g x B) _ a).negative i)
        (chosenOf P (substituted s g x B) hD _ g.positionLog (ofSymmetric C) (Sum.inl ((clausesOf P (substituted s g x B) _ a).name i)) r) := by
    intro i
    rw [Guess.family_x, literal_eval_eq, assignment_eq4]
    rfl
  have hy : ((baseGuess4 s P g x B hD C pub hn W).family P x).y a r =
      chosenOf P (substituted s g x B) hD _ g.positionLog (ofSymmetric C) (Sum.inr a) r := helper_eq4 s P g x B hD C pub hn W a r
  rw [hx 0, hx 1, hx 2, hy]
  rfl

end Construct

/-! ## Part 4: useful witnesses and `U < γ − ε` -/

section Final
variable (s : GateSources) (P : ThreeQueryPCPP) (g : GateParams) {N : ℕ} (x : BitInput N)
  (B : Outer.OuterGuess (width s g N)) (hD : ∀ r, (substituted s g x B).D.eval r = true)
  (C : SymmetricThresholdCircuit
    ((substituted s g x B).n + clauseWidth g.clauseDegree (width s g N) + g.positionLog))
  (pub : ThresholdNormalizationContract) (hn : 1 ≤ width s g N) {B1 B2 : ℕ} (ctr : Counter B1 B2) (ω : ℚ)

/-- Useful witness prefixes: per term, a witness of radius at most `ω` for its call, when one exists. -/
noncomputable def usefulWit4 (a : ℕ) (t : Fin 10) : List Bool := by
  classical
  exact if h : ∃ w : List Bool, w.length ≤ ctr.witnessLength (width s g N) ∧
      ∀ c, (baseGuess4 s P g x B hD C pub hn (fun _ _ => [])).callOf P x ω
        ((baseGuess4 s P g x B hD C pub hn (fun _ _ => [])).operands P x a t) = some c →
        (ctr.value c w).2 ≤ ω
    then Classical.choose h else []

/-- The guess of the approximator: chosen cofactors and useful witnesses. -/
noncomputable abbrev approxGuess4 : Guess (width s g N) :=
  baseGuess4 s P g x B hD C pub hn (usefulWit4 s P g x B hD C pub hn ctr ω)

/-- Calls and operands do not read the witness prefixes. -/
theorem callOf_base4 (W W' : ℕ → Fin 10 → List Bool) (a : ℕ) (t : Fin 10) :
    (baseGuess4 s P g x B hD C pub hn W).callOf P x ω ((baseGuess4 s P g x B hD C pub hn W).operands P x a t) =
      (baseGuess4 s P g x B hD C pub hn W').callOf P x ω ((baseGuess4 s P g x B hD C pub hn W').operands P x a t) := by
  rfl

theorem usefulWit_length4 (a : ℕ) (t : Fin 10) :
    (usefulWit4 s P g x B hD C pub hn ctr ω a t).length ≤ ctr.witnessLength (width s g N) := by
  unfold usefulWit4
  split_ifs with h
  · exact (Classical.choose_spec h).1
  · simp

theorem usefulWit_spec4 (a : ℕ) (t : Fin 10)
    (hex : ∃ w : List Bool, w.length ≤ ctr.witnessLength (width s g N) ∧
      ∀ c, (baseGuess4 s P g x B hD C pub hn (fun _ _ => [])).callOf P x ω
        ((baseGuess4 s P g x B hD C pub hn (fun _ _ => [])).operands P x a t) = some c →
        (ctr.value c w).2 ≤ ω) :
    ∀ c, (baseGuess4 s P g x B hD C pub hn (fun _ _ => [])).callOf P x ω
        ((baseGuess4 s P g x B hD C pub hn (fun _ _ => [])).operands P x a t) = some c →
        (ctr.value c (usefulWit4 s P g x B hD C pub hn ctr ω a t)).2 ≤ ω := by
  unfold usefulWit4
  rw [dif_pos hex]
  exact (Classical.choose_spec hex).2

/-- `thm:counter` (ii) supplies a useful witness for every term of every gadget (`lem:ae-estimate` (iii)). -/
theorem useful_exists4 (aC : ℝ) (onsetC : ℕ)
    (hcomplete : ∀ c : Call, onsetC ≤ c.n → Admitted4 B1 B2 c →
      (callWires c : ℝ) ≤ aC * (c.radius : ℝ) * A4 c.n →
      ∃ w : List Bool, w.length ≤ ctr.witnessLength c.n ∧ (ctr.value c w).2 ≤ c.radius)
    (b : ℕ) (hC : C.wireCount ≤ b) (hq4 : 4 ≤ width s g N) (hon : onsetC ≤ width s g N)
    (hb4 : b ≤ width s g N ^ 4) (hr1 : 1 ≤ ω * (width s g N : ℚ) ^ B1) (hr2 : ω ≤ 1 / 16)
    (hr3 : (ratWord ω).length ≤ width s g N ^ B2)
    (hA4 : (2 * b : ℝ) ≤ aC * (ω : ℝ) * A4 (width s g N))
    (a : ℕ) (ha : a < gadgets s g N) (t : Fin 10) :
    ∃ w : List Bool, w.length ≤ ctr.witnessLength (width s g N) ∧
      ∀ c, (baseGuess4 s P g x B hD C pub hn (fun _ _ => [])).callOf P x ω
        ((baseGuess4 s P g x B hD C pub hn (fun _ _ => [])).operands P x a t) = some c →
        (ctr.value c w).2 ≤ ω := by
  cases hco : (baseGuess4 s P g x B hD C pub hn (fun _ _ => [])).callOf P x ω
      ((baseGuess4 s P g x B hD C pub hn (fun _ _ => [])).operands P x a t) with
  | none => exact ⟨[], by simp, fun c hc => by simp at hc⟩
  | some c =>
    obtain ⟨hcn, hcr⟩ := Guess.callOf_n_radius P x (baseGuess4 s P g x B hD C pub hn (fun _ _ => [])) ω _ c hco
    have hwf : ∀ o ∈ (baseGuess4 s P g x B hD C pub hn (fun _ _ => [])).operands P x a t, ∀ j, o.2 = .aux j →
        ((baseGuess4 s P g x B hD C pub hn (fun _ _ => [])).circuits j).WellFormed (Call.B0 (width s g N)) ∧
          UnitTop ((baseGuess4 s P g x B hD C pub hn (fun _ _ => [])).circuits j) ∧
          wires ((baseGuess4 s P g x B hD C pub hn (fun _ _ => [])).circuits j) ≤ b := by
      intro o ho j hj
      have hjlt := Guess.operands_aux_lt P x (baseGuess4 s P g x B hD C pub hn (fun _ _ => [])) a ha t o ho j hj
      obtain ⟨hw, hu, ht⟩ := proofCircuits_good4 s P g x B hD C pub hn (fun _ _ => []) j hjlt
      exact ⟨hw, hu, ht.trans hC⟩
    obtain ⟨hadm, hW2⟩ := Guess.callOf_admitted4 P x (baseGuess4 s P g x B hD C pub hn (fun _ _ => []))
      ω b _ c hco hwf hq4 hb4 hr1 hr2 hr3
    have hcap : (callWires c : ℝ) ≤ aC * (c.radius : ℝ) * A4 c.n := by
      rw [hcr, hcn]
      calc (callWires c : ℝ) ≤ ((2 * b : ℕ) : ℝ) := by exact_mod_cast hW2
        _ = 2 * (b : ℝ) := by push_cast; ring
        _ ≤ _ := hA4
    obtain ⟨w, hwl, hwr⟩ := hcomplete c (by rw [hcn]; exact hon) hadm hcap
    refine ⟨w, by rw [← hcn]; exact hwl, fun c' hc' => ?_⟩
    cases hc'
    rw [← hcr]
    exact hwr

theorem approx_complete4 (aC : ℝ) (onsetC : ℕ)
    (hcomplete : ∀ c : Call, onsetC ≤ c.n → Admitted4 B1 B2 c →
      (callWires c : ℝ) ≤ aC * (c.radius : ℝ) * A4 c.n →
      ∃ w : List Bool, w.length ≤ ctr.witnessLength c.n ∧ (ctr.value c w).2 ≤ c.radius)
    (budget : ℕ → ℕ) (ε εT : ℝ) (hC : C.wireCount ≤ budget (width s g N))
    (hagree : 1 - (P.gamma : ℝ) / 5 + ε ≤ NearCubicWires.agreement C.eval
      (hardTable P (substituted s g x B) hD (clauseWidth g.clauseDegree (width s g N)) g.positionLog))
    (hε : 0 < ε) (hε1 : ε < 1) (hεγ : ε < (P.gamma : ℝ) / 5) (hεT : εT ≤ 2 * ε) (hω0 : 0 ≤ ω)
    (hωε : (ω : ℝ) ≤ ε / 128)
    (hP5 : 5 ≤ 2 ^ g.positionLog) (hP : 128 ≤ ε * ((2 ^ g.positionLog : ℕ) : ℝ))
    (hq4 : 4 ≤ width s g N) (hon : onsetC ≤ width s g N) (hb4 : budget (width s g N) ≤ width s g N ^ 4)
    (hr1 : 1 ≤ ω * (width s g N : ℚ) ^ B1) (hr2 : ω ≤ 1 / 16) (hr3 : (ratWord ω).length ≤ width s g N ^ B2)
    (hA4 : (2 * budget (width s g N) : ℝ) ≤ aC * (ω : ℝ) * A4 (width s g N))
    (hsrc : B.src.size ≤ RecoveryScheduleEnvelope.oracleSizeBound g.degree (width s g N))
    (hpf : B.pf.size ≤ RecoveryScheduleEnvelope.oracleSizeBound g.degree (width s g N))
    (hrb : (pcpp s P g x B).randomBits ≤ clauseWidth g.clauseDegree (width s g N))
    (hν1 : 1 ≤ nu N) (hprec : (P.gamma : ℝ) / (Outer.instLength g.lenExp (nu N) : ℝ) < εT)
    (hS : (approxGuess4 s P g x B hD C pub hn ctr ω).SetupOK x) :
    (approxGuess4 s P g x B hD C pub hn ctr ω).Guards P x ctr budget εT ∧
      (approxGuess4 s P g x B hD C pub hn ctr ω).SizeOK P x ctr budget ∧
      (approxGuess4 s P g x B hD C pub hn ctr ω).upperEstimate P x ctr ω < (P.gamma : ℝ) - εT := by
  have hex := fun (a : ℕ) (ha : a < gadgets s g N) (t : Fin 10) =>
    useful_exists4 s P g x B hD C pub hn ctr ω aC onsetC hcomplete (budget (width s g N)) hC hq4 hon hb4 hr1 hr2 hr3
      hA4 a ha t
  refine ⟨⟨hrb, by omega, hν1, hprec, hS⟩,
    ⟨hsrc, hpf, fun j hj => ?_, fun a _ t => usefulWit_length4 s P g x B hD C pub hn ctr ω a t⟩, ?_⟩
  · obtain ⟨hw, hu, ht⟩ := proofCircuits_good4 s P g x B hD C pub hn _ j hj
    exact ⟨hw, (topWeight_le_wires hw hu).trans (ht.trans hC)⟩
  haveI : Nonempty (Fin (gadgets s g N)) := finTwoPowNonempty _
  have hsound := Guess.termInterval_sound P x (approxGuess4 s P g x B hD C pub hn ctr ω) ctr ω
  have hrad : ∀ (a : Fin (gadgets s g N)) (t : Fin 10),
      (((approxGuess4 s P g x B hD C pub hn ctr ω).termInterval P x ctr ω a.val t).2 : ℝ) ≤ (ω : ℝ) := by
    intro a t
    have h := Guess.intervalOf_radius P x (approxGuess4 s P g x B hD C pub hn ctr ω) ctr ω hω0
      (usefulWit4 s P g x B hD C pub hn ctr ω a.val t)
      ((approxGuess4 s P g x B hD C pub hn ctr ω).operands P x a.val t)
      (Guess.operands_length P x _ a.val t)
      (fun c hc => usefulWit_spec4 s P g x B hD C pub hn ctr ω a.val t (hex a.val a.isLt t) c
        (by rw [callOf_base4 s P g x B hD C pub hn ω (fun _ _ => []) (usefulWit4 s P g x B hD C pub hn ctr ω)]; exact hc))
    exact_mod_cast h
  have hup := upper_le ((approxGuess4 s P g x B hD C pub hn ctr ω).family P x)
    (fun (a : Fin (gadgets s g N)) (t : Fin 10) => (approxGuess4 s P g x B hD C pub hn ctr ω).termInterval P x ctr ω a.val t)
    hsound (ω : ℝ) hrad
  rw [meanPenalty_eq4] at hup
  have hpen := chosen_penalty_bound P (substituted s g x B) hD (clauseWidth g.clauseDegree (width s g N))
    g.positionLog (ofSymmetric C) hP5
  have hcyc := cycle_factor (2 ^ g.positionLog) ε hP5 hε hε1 hP
  have hagreeW : NearCubicWires.agreement C.eval
      (hardTable P (substituted s g x B) hD (clauseWidth g.clauseDegree (width s g N)) g.positionLog) =
      FiniteAverages.agreement (ofSymmetric C).eval
      (hardTable P (substituted s g x B) hD (clauseWidth g.clauseDegree (width s g N)) g.positionLog) := by
    rw [ofSymmetric_eval_fun, finiteAgreement_eq]
  have herr : error (hardTable P (substituted s g x B) hD (clauseWidth g.clauseDegree (width s g N)) g.positionLog)
      (ofSymmetric C).eval ≤ (P.gamma : ℝ) / 5 - ε := by
    have h1 := error_add_agreement (hardTable P (substituted s g x B) hD
      (clauseWidth g.clauseDegree (width s g N)) g.positionLog) (ofSymmetric C).eval
    rw [hagreeW, agreement_comm] at hagree
    linarith
  have herr0 := error_nonneg (hardTable P (substituted s g x B) hD
      (clauseWidth g.clauseDegree (width s g N)) g.positionLog) (ofSymmetric C).eval
  have hγ1 : (P.gamma : ℝ) < 1 := by exact_mod_cast P.gamma_lt_one
  set δ := error (hardTable P (substituted s g x B) hD (clauseWidth g.clauseDegree (width s g N)) g.positionLog) (ofSymmetric C).eval
  set κ := (((2 ^ g.positionLog : ℕ) : ℝ) / ((2 ^ g.positionLog) / 5 : ℕ))
  have hU : (approxGuess4 s P g x B hD C pub hn ctr ω).upperEstimate P x ctr ω ≤ κ * δ + 10 * (ω : ℝ) := by
    show upper _ ≤ _
    linarith
  have h1 : κ * δ ≤ (5 + ε) * δ := mul_le_mul_of_nonneg_right hcyc herr0
  have h2 : (5 + ε) * δ ≤ (5 + ε) * ((P.gamma : ℝ) / 5 - ε) := mul_le_mul_of_nonneg_left herr (by linarith)
  nlinarith

end Final

end NearQuarticWires.Worker4.Worker
