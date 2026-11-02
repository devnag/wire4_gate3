import Proof.Quartic.Control.Fits
import Proof.Gates.CounterAsm.Main

/-!
# The cost of reading the number of rounds

Paper: `prop:time`, paper/paper.tex: parameter handling is polynomial and Step 3 costs `2S` child
evaluations; `sec:params`: `S = 2mℓ_f ≥ 2mk`, `k = r·⌊log₂(n/r + 1)⌋`, `r = 16μ`.

Skipping a list of `m` numbers reads its count `m` in unary (`ParseNat.readNatM`), which costs
`(L+2)(40·2^L + 40)` with `L = natBitLength m`, i.e. `O(m log m)`. Over the whole call word this is
`O(|callWord| · log |callWord|)` (`circuitCost_le`, `readCost_le`). The logarithm is paid by the rounds:
`natBitLength n ≤ S + 1` (`natBitLength_le_rounds`), and the call word has polynomial length
(`callBound_le`, `natBitLength_callBound_le`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Control

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces (listWord gateWord bitWord circuitWord NCircuit Call callWord kindTag)
open NearCubicGates.Close.Codec (skipListCost circuitCost gateCost intCost bitCost skipIntCost)

local notation "intWord" => NearCubicGates.Close.Interfaces.intWord

/-! ## Bit lengths -/

theorem natBitLength_le_of_lt_pow {y E : ℕ} (hE : 1 ≤ E) (h : y < 2 ^ E) : natBitLength y ≤ E := by
  unfold natBitLength
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · simp; omega
  · have := Nat.log_lt_of_lt_pow (by omega) h
    omega

theorem natBitLength_mono {a b : ℕ} (h : a ≤ b) : natBitLength a ≤ natBitLength b := by
  unfold natBitLength; have := Nat.log_mono_right (b := 2) h; omega

theorem two_pow_natBitLength_le (m : ℕ) : 2 ^ natBitLength m ≤ 2 * m + 2 := by
  unfold natBitLength
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have := Nat.pow_log_le_self 2 (show m ≠ 0 by omega)
    rw [pow_succ]; omega

theorem natBitLength_le_self_succ (m : ℕ) : natBitLength m ≤ m + 1 :=
  natBitLength_le_of_lt_pow (by omega) (lt_trans Nat.lt_two_pow_self (Nat.pow_lt_pow_right (by norm_num) (by omega)))

/-! ## Skipping a list -/

theorem sum_map_le {α : Type} (xs : List α) (f g : α → ℕ) (h : ∀ x ∈ xs, f x ≤ g x) :
    (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    have := h x (by simp); have := ih (fun y hy => h y (by simp [hy])); omega

theorem sum_map_add {α : Type} (xs : List α) (f : α → ℕ) (c : ℕ) :
    (xs.map fun x => f x + c).sum = (xs.map f).sum + c * xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; ring

theorem sum_map_mul_length {α : Type} (g : α → List Bool) (xs : List α) (K : ℕ) :
    (xs.map fun x => K * (g x).length).sum = K * (xs.flatMap g).length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih, List.flatMap_cons, List.length_append]; ring

/-- **Skipping a list**: if each element costs at most `A (Λ+2)` per cell and the count has bit length at most `Λ`,
the list costs at most `(A + 210)(Λ+2)` per cell. -/
theorem skipListCost_le {α : Type} (g : α → List Bool) (cost : α → ℕ) (xs : List α) (A Λ : ℕ)
    (hg : ∀ x, 1 ≤ (g x).length) (hΛ : natBitLength xs.length ≤ Λ)
    (hc : ∀ x ∈ xs, cost x ≤ A * (Λ + 2) * (g x).length) :
    skipListCost xs.length (xs.map cost) ≤ (A + 210) * (Λ + 2) * (listWord g xs).length := by
  unfold skipListCost
  have hmF : xs.length ≤ (xs.flatMap g).length := count_le_flatMap g xs hg
  have hpow := two_pow_natBitLength_le xs.length
  have hlist : (listWord g xs).length ≥ (xs.flatMap g).length + 1 := by
    unfold listWord; simp only [List.length_append]; have := natWord_pos xs.length; omega
  have h1 : (natBitLength xs.length + 2) * (40 * 2 ^ natBitLength xs.length + 40) ≤
      (Λ + 2) * (80 * (xs.flatMap g).length + 120) := Nat.mul_le_mul (by omega) (by omega)
  have h3 := sum_map_le xs cost (fun x => A * (Λ + 2) * (g x).length) hc
  rw [sum_map_mul_length] at h3
  have h2 : ((xs.map cost).map fun c => c + 4).sum = (xs.map cost).sum + 4 * xs.length := by
    rw [List.map_map]
    have := sum_map_add xs cost 4
    simp only [Function.comp_def] at this ⊢
    rw [this]
  rw [h2]
  have h4 : (Λ + 2) * (80 * (xs.flatMap g).length + 120) + A * (Λ + 2) * (xs.flatMap g).length +
      4 * (xs.flatMap g).length + 3 ≤ (A + 210) * (Λ + 2) * ((xs.flatMap g).length + 1) := by
    nlinarith
  have h5 : (A + 210) * (Λ + 2) * ((xs.flatMap g).length + 1) ≤ (A + 210) * (Λ + 2) * (listWord g xs).length :=
    Nat.mul_le_mul_left _ hlist
  omega

/-! ## Skipping the call word -/

theorem intCost_le (z : ℤ) : intCost z ≤ 16 * (intWord z).length := by
  unfold intCost skipIntCost
  rw [intWord_length]
  have : natBitLength (if z < 0 then 1 else 0) ≤ 1 := by split_ifs <;> simp [natBitLength]
  omega

theorem bitCost_le (b : Bool) : bitCost b ≤ 20 * (bitWord b).length := by
  unfold bitCost bitWord
  rw [NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length]
  have : natBitLength (if b then 1 else 0) ≤ 1 := by split_ifs <;> simp [natBitLength]
  omega

theorem natCost_le (x : ℕ) : 20 * natBitLength x + 20 ≤ 20 * (natWord x).length := by
  have := natBitLength_le_natWord x; omega

theorem gateCost_le {n : ℕ} (gt : NormalizedThresholdGate n) (Λ : ℕ) (hΛ : natBitLength n ≤ Λ) :
    gateCost gt ≤ 227 * (Λ + 2) * (gateWord gt).length := by
  unfold gateCost
  have hl := skipListCost_le intWord intCost (List.ofFn gt.weight) 16 Λ intWord_pos
    (by rw [List.length_ofFn]; exact hΛ) (fun z _ => by
      have hz := intCost_le z
      calc intCost z ≤ 16 * (intWord z).length := hz
        _ ≤ 16 * (Λ + 2) * (intWord z).length := by nlinarith)
  rw [List.length_ofFn] at hl
  have ht := intCost_le gt.threshold
  have hg : (gateWord gt).length = (listWord intWord (List.ofFn gt.weight)).length + (intWord gt.threshold).length := by
    unfold gateWord; simp only [List.length_append]
  have := intWord_pos gt.threshold
  rw [hg]; nlinarith

/-- **Skipping a circuit** costs at most `440 (Λ+2)` per cell, `Λ` bounding the bit lengths of its counts. -/
theorem circuitCost_le {n : ℕ} (C : NCircuit n) (Λ : ℕ) (hn : natBitLength n ≤ Λ)
    (hG : natBitLength C.gates.length ≤ Λ) (hK : natBitLength C.coeffs.length ≤ Λ)
    (hT : natBitLength C.table.length ≤ Λ) :
    circuitCost C ≤ 440 * (Λ + 2) * (circuitWord C).length := by
  unfold circuitCost
  have h1 := skipListCost_le gateWord gateCost C.gates 227 Λ gateWord_pos hG (fun gt _ => gateCost_le gt Λ hn)
  have h2 := skipListCost_le intWord intCost C.coeffs 16 Λ intWord_pos hK (fun z _ => by
    have := intCost_le z
    calc intCost z ≤ 16 * (intWord z).length := this
      _ ≤ 16 * (Λ + 2) * (intWord z).length := by nlinarith)
  have h3 := skipListCost_le bitWord bitCost C.table 20 Λ bitWord_pos hT (fun b _ => by
    have := bitCost_le b
    calc bitCost b ≤ 20 * (bitWord b).length := this
      _ ≤ 20 * (Λ + 2) * (bitWord b).length := by nlinarith)
  have hc : (circuitWord C).length = (listWord gateWord C.gates).length + (listWord intWord C.coeffs).length +
      (listWord bitWord C.table).length := by unfold circuitWord; simp only [List.length_append]
  have hpos : 1 ≤ (listWord gateWord C.gates).length := by
    unfold listWord; simp only [List.length_append]; have := natWord_pos C.gates.length; omega
  rw [hc]
  have e1 : skipListCost C.gates.length (C.gates.map gateCost) ≤
      440 * (Λ + 2) * (listWord gateWord C.gates).length := le_trans h1 (Nat.mul_le_mul_right _ (by omega))
  have e2 : skipListCost C.coeffs.length (C.coeffs.map intCost) ≤
      440 * (Λ + 2) * (listWord intWord C.coeffs).length := le_trans h2 (Nat.mul_le_mul_right _ (by omega))
  have e3 : skipListCost C.table.length (C.table.map bitCost) ≤
      440 * (Λ + 2) * (listWord bitWord C.table).length := le_trans h3 (Nat.mul_le_mul_right _ (by omega))
  have e4 : 2 ≤ 440 * (Λ + 2) * (listWord gateWord C.gates).length := by nlinarith
  nlinarith


theorem natsCost_le (xs : List ℕ) : natsCost xs ≤ 21 * (xs.flatMap natWord).length := by
  unfold natsCost
  have h := sum_map_le xs (fun x => 20 * natBitLength x + 21) (fun x => 21 * (natWord x).length)
    (fun x _ => by have := natBitLength_le_natWord x; omega)
  rw [sum_map_mul_length] at h
  exact h

/-- **The cost of reading `S`**: `O((log(|callWord| + n) + 2)·|callWord|)` for the call word, linear in the nineteen
numbers, `O(S²)` for `S`. -/
theorem readCost_le (c : Call) (xs : List ℕ) (S : ℕ) :
    readCost c xs S ≤ 440 * (natBitLength ((callWord c).length + c.n) + 2) * ((callWord c).length + 1) +
      21 * (xs.flatMap natWord).length + (S + 3) * (80 * S + 120) + 20 := by
  set Λ := natBitLength ((callWord c).length + c.n) with hΛ
  have hcl := congrArg List.length (callWord_split c)
  simp only [List.length_append] at hcl
  have hnb : ∀ m, m ≤ (callWord c).length + c.n → natBitLength m ≤ Λ := fun m hm => natBitLength_mono hm
  have hn := natBitLength_le_natWord c.n
  have hfirst := listWord_count gateWord c.first.gates gateWord_pos
  have hfirstK := listWord_count intWord c.first.coeffs intWord_pos
  have hfirstT := listWord_count bitWord c.first.table bitWord_pos
  have hsecond := listWord_count gateWord c.second.gates gateWord_pos
  have hsecondK := listWord_count intWord c.second.coeffs intWord_pos
  have hsecondT := listWord_count bitWord c.second.table bitWord_pos
  have hc1 : (listWord gateWord c.first.gates).length + (listWord intWord c.first.coeffs).length +
      (listWord bitWord c.first.table).length = (circuitWord c.first).length := by
    unfold circuitWord; simp only [List.length_append]
  have hc2 : (listWord gateWord c.second.gates).length + (listWord intWord c.second.coeffs).length +
      (listWord bitWord c.second.table).length = (circuitWord c.second).length := by
    unfold circuitWord; simp only [List.length_append]
  have C1 := circuitCost_le c.first Λ (hnb _ (by omega)) (hnb _ (by omega)) (hnb _ (by omega)) (hnb _ (by omega))
  have C2 := circuitCost_le c.second Λ (hnb _ (by omega)) (hnb _ (by omega)) (hnb _ (by omega)) (hnb _ (by omega))
  have hP := listWord_count natWord c.parity natWord_pos
  have P1 := skipListCost_le natWord (fun x => 20 * natBitLength x + 20) c.parity 20 Λ natWord_pos
    (hnb _ (by omega)) (fun x _ => by
      have h := natCost_le x
      calc 20 * natBitLength x + 20 ≤ 20 * (natWord x).length := h
        _ ≤ 20 * (Λ + 2) * (natWord x).length := by nlinarith)
  have I1 := intCost_le c.radius.num
  have N1 := natCost_le c.n
  have N2 := natCost_le (kindTag c.kind)
  have N3 := natCost_le c.radius.den
  have hX := natsCost_le xs
  have hS1 := natBitLength_le_self_succ S
  have hS2 := two_pow_natBitLength_le S
  have hSt : (natBitLength S + 2) * (40 * 2 ^ natBitLength S + 40) ≤ (S + 3) * (80 * S + 120) :=
    Nat.mul_le_mul (by omega) (by omega)
  unfold readCost
  have hI : NearCubicGates.Close.Codec.skipIntCost c.radius.num ≤ 16 * (intWord c.radius.num).length := I1
  have hL2 : 2 ≤ Λ + 2 := by omega
  nlinarith


/-! ## The logarithm is paid by the rounds -/

/-- The call word of a normalized call has polynomial length (`CounterAsm.callBound`). -/
theorem callBound_le (B2 n : ℕ) : NearCubicGates.Close.CounterAsm.callBound B2 n ≤ 2 ^ 11 * (n + 1) ^ (B2 + 9) := by
  unfold NearCubicGates.Close.CounterAsm.callBound
  set N := n + 1 with hN
  have hN1 : 1 ≤ N := by omega
  have p : ∀ a b, a ≤ b → N ^ a ≤ N ^ b := fun a b h => Nat.pow_le_pow_right hN1 h
  have f1 : 14 + N + 4 * N ^ 4 * (2 * N + 7) ≤ 51 * N ^ 5 := by
    have h0 := p 0 5; have h1 := p 1 5; have h4 := p 4 5
    have e : 4 * N ^ 4 * (2 * N + 7) = 8 * N ^ 5 + 28 * N ^ 4 := by ring
    simp only [pow_zero, pow_one] at h0 h1
    rw [e]; omega
  have f2 : 2 * (4 * N ^ 2 + 4 * N ^ 4 + 2 * N + 4 + N ^ B2) + 1 ≤ 31 * N ^ (B2 + 4) := by
    have h0 := p 0 (B2 + 4); have h1 := p 1 (B2 + 4); have h2 := p 2 (B2 + 4); have h4 := p 4 (B2 + 4)
    have hB := p B2 (B2 + 4)
    simp only [pow_zero, pow_one] at h0 h1
    omega
  calc (14 + N + 4 * N ^ 4 * (2 * N + 7)) * (2 * (4 * N ^ 2 + 4 * N ^ 4 + 2 * N + 4 + N ^ B2) + 1)
      ≤ (51 * N ^ 5) * (31 * N ^ (B2 + 4)) := Nat.mul_le_mul f1 f2
    _ = 1581 * N ^ (B2 + 9) := by ring
    _ ≤ 2 ^ 11 * N ^ (B2 + 9) := by
      have : 1581 ≤ 2 ^ 11 := by norm_num
      exact Nat.mul_le_mul_right _ this

/-- A number below `2^c (n+1)^D` has bit length at most `c + D · natBitLength (n+1)`. -/
theorem natBitLength_poly_le (y c D n : ℕ) (h : y ≤ 2 ^ c * (n + 1) ^ D) :
    natBitLength y ≤ c + 1 + D * natBitLength (n + 1) := by
  apply natBitLength_le_of_lt_pow (by omega)
  have h1 : n + 1 < 2 ^ natBitLength (n + 1) := by
    unfold natBitLength; exact Nat.lt_pow_succ_log_self (by norm_num) _
  have h2 : (n + 1) ^ D ≤ (2 ^ natBitLength (n + 1)) ^ D := Nat.pow_le_pow_left h1.le D
  calc y ≤ 2 ^ c * (n + 1) ^ D := h
    _ ≤ 2 ^ c * (2 ^ natBitLength (n + 1)) ^ D := Nat.mul_le_mul_left _ h2
    _ = 2 ^ (c + natBitLength (n + 1) * D) := by rw [← pow_mul, ← pow_add]
    _ < 2 ^ (c + 1 + D * natBitLength (n + 1)) :=
      Nat.pow_lt_pow_right (by norm_num) (by rw [Nat.mul_comm]; omega)

/-- **The bit length of `n` is paid by the rounds** (`sec:params`): with `r = 16μ ≥ 16`,
`4r ≤ n`, `s = ⌊log₂(n/r + 1)⌋`, `k = rs` and `S = 8 max(k, Q_exp + 1)`, the input length has
`natBitLength n ≤ S + 1`. -/
theorem natBitLength_le_rounds (n mu r s k S ellf Qexp : ℕ) (hmu : 1 ≤ mu) (hr : r = 16 * mu) (hrb : 4 * r ≤ n)
    (hs : s = Nat.log 2 (n / r + 1)) (hk : k = r * s) (hel : ellf = max k (Qexp + 1)) (hS : S = 2 * 4 * ellf) :
    natBitLength n ≤ S + 1 := by
  have hr1 : 16 ≤ r := by omega
  have hdiv : n < r * (n / r + 1) := Nat.lt_mul_div_succ n (by omega)
  have hlog : n / r + 1 < 2 ^ (s + 1) := by rw [hs]; exact Nat.lt_pow_succ_log_self (by norm_num) _
  have hs1 : 1 ≤ s := by
    rw [hs]
    have : 4 ≤ n / r := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
    exact Nat.le_log_of_pow_le (by norm_num) (by omega)
  have hrpow : r < 2 ^ r := Nat.lt_two_pow_self
  have hn : n < 2 ^ (r + s + 1) := by
    calc n < r * (n / r + 1) := hdiv
      _ ≤ r * 2 ^ (s + 1) := Nat.mul_le_mul_left _ hlog.le
      _ ≤ 2 ^ r * 2 ^ (s + 1) := Nat.mul_le_mul_right _ hrpow.le
      _ = 2 ^ (r + s + 1) := by rw [← pow_add]; ring_nf
  have hb := natBitLength_le_of_lt_pow (by omega) hn
  have hrs : r + s ≤ 2 * k := by rw [hk]; nlinarith
  have hkS : k ≤ ellf := by rw [hel]; exact le_max_left _ _
  omega

/-- The bit length of `|callWord| + n` is linear in `S` on a call whose parameters follow the rules. -/
theorem natBitLength_call_le (B2 n w S : ℕ) (hw : w ≤ NearCubicGates.Close.CounterAsm.callBound B2 n)
    (hS : natBitLength n ≤ S + 1) : natBitLength (w + n) ≤ (2 * B2 + 32) * (S + 1) := by
  have h1 : w + n ≤ 2 ^ 12 * (n + 1) ^ (B2 + 9) := by
    have := callBound_le B2 n
    have h2 : n + 1 ≤ (n + 1) ^ (B2 + 9) := by
      calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
        _ ≤ (n + 1) ^ (B2 + 9) := Nat.pow_le_pow_right (by omega) (by omega)
    rw [show (2 : ℕ) ^ 12 = 2 * 2 ^ 11 by norm_num]
    nlinarith
  have h2 := natBitLength_poly_le (w + n) 12 (B2 + 9) n h1
  have h3 : natBitLength (n + 1) ≤ natBitLength n + 1 := by
    have : n + 1 < 2 ^ (natBitLength n + 1) := by
      unfold natBitLength
      have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n
      rw [pow_succ]; omega
    exact natBitLength_le_of_lt_pow (by omega) this
  have h4 : (B2 + 9) * natBitLength (n + 1) ≤ (B2 + 9) * (S + 2) := Nat.mul_le_mul_left _ (by omega)
  nlinarith

end NearQuarticWires.Control
