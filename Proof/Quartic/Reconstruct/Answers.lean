import Proof.Quartic.Reconstruct.Phases

/-!
# The answers of the solver on the listed systems

Paper: Step 3 of `sec:algorithm`, paper/paper.tex, with step (1) of the proof of `prop:sound` (`imp:window`: the system has exactly one solution supported in the box).

On a listed system (`systemList`: a certified column, `κ_σ ≠ 0`, a digit vector `δ`), every exact solver returns a
solution (the class function solves the system), and by `imp:window` every entry of it is the value of the class
function at the corresponding point of `Bx(δ)` (`solve_entries`): an integer of absolute value below `p^e`.
Hence the answer of every exact solver on a listed system has polynomial size (`solveWord_length_le`), whatever its
cost: the stages that read the answers (`ReconstructPhases.solved`, `ReconstructPhases.total`) need only words of
size `(n+1)^{e₁}`.

Finally, each word between two stages has length at most a polynomial in `n` times the cost of the stages that write
and read it (`printsWord_length_le`, `tablesWord_length_le`, `systemsWord_length_le`, `solvedWord_length_le`).
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open Finset
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Interfaces
open NearQuarticWires.Greedy NearQuarticWires.Program
open NearCubicGates.Close.Interfaces.Formats (SysReq SysSolves SolveMachine inClass sysWord solveWord)

variable {B1 B2 : ℕ}

theorem mem_systemList {q : ChildRequest B1 B2} {x : SystemIndex q} (hx : x ∈ systemList q) :
    Cycle.kappa Algorithm.traceOrder x.2.1 ≠ 0 ∧ x.2.2.1 ∈ digitSet q ∧
      x.2.2.2 ∈ q.cellCall.certifiedColumns := by
  obtain ⟨s, -, hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨σ, hσ, hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨δ, hδ, hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
  exact ⟨(mem_activePatterns σ).mp hσ, (mem_digitList q δ).mp hδ, (mem_certList q z).mp hz⟩

section Entries

variable (C : Algorithm.CellCall)

/-- **Every entry of the answer is a class value** (Step 3, with `imp:window`): on a certified
column, for `κ_σ ≠ 0`, a digit vector `δ` and a system encoding the system of the part `s`, every exact solver
returns a solution, and each of its entries is the value of the class function at a point of `Bx(δ)`. -/
theorem solve_entries (S : SolveMachine) (sys : SysReq) (H : C.ReconstructionHypotheses) (π : List Bool)
    (hπ : π.length ≤ C.seedLength) (s : Bool) (z : Fin C.ncol) (hz : z ∈ C.certifiedColumns)
    (σ : Cycle.SignPattern Algorithm.traceOrder) (hσ : Cycle.kappa Algorithm.traceOrder σ ≠ 0)
    (δ : Fin 2 → Fin (C.J + 1) → ℤ) (hδ : δ ∈ C.digitVectors z) (henc : SystemEncodes C sys π s z σ δ) :
    ∃ F, S.solve sys = some F ∧ F.length = sys.pts.length ∧
      ∀ f ∈ F, ∃ y ∈ C.box z δ, f = (classValueOf C (splitWeight C π s) z σ δ y : ℚ) := by
  classical
  have hcert : C.Certified z := by
    unfold Algorithm.CellCall.certifiedColumns at hz
    exact (Finset.mem_filter.mp hz).2
  set Fstar : (Fin 2 → ℤ) → ℚ := fun y => (classValueOf C (splitWeight C π s) z σ δ y : ℚ) with hFstar
  obtain ⟨hs1, hs2⟩ := classValueOf_solves C H π hπ s z hcert σ hσ δ hδ
  have hnonneg : ∀ p ∈ C.primes, ∀ ρY ∈ C.residueVectors z p,
      0 ≤ recoveredCountOf C (splitWeight C π s) z σ p δ ρY :=
    fun p hp ρY hρ => recoveredCountOf_nonneg C H π hπ s z hcert σ hσ δ hδ p hp ρY hρ
  let vecOf : List ℤ → (Fin 2 → ℤ) := fun u j => u.getD j.val 0
  have hvec : ∀ y, vecOf (pointList y) = y := by
    intro y
    funext j
    fin_cases j <;> rfl
  have hrow : ∀ (F : List ℚ), F.length = sys.pts.length → ∀ p ∈ C.primes, ∀ ρY ∈ C.residueVectors z p,
      (((sys.pts.zip F).filter fun uf => inClass p [(ρY 0).toNat, (ρY 1).toNat] uf.1).map Prod.snd).sum =
        ∑ y ∈ (C.box z δ).filter (fun y => ∀ j, y j ≡ ρY j [ZMOD (p : ℤ)]),
          pointValue sys.pts F (pointList y) := by
    intro F hF p _ ρY hρ
    rw [sum_filter_zip _ sys.pts F henc.nodup hF, sum_pts_eq_sum_box C henc.mem_pts]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext y
    simp only [Finset.mem_filter]
    rw [inClass_pointList p ρY (residueVectors_nonneg C hρ) y]
  have hsolve0 : SysSolves sys (sys.pts.map fun u => Fstar (vecOf u)) := by
    refine ⟨by simp, fun row hrowmem => ?_⟩
    obtain ⟨p, hp, ρY, hρ, rfl⟩ := henc.rows_sound row hrowmem
    simp only [systemRow]
    rw [hrow _ (by simp) p hp ρY hρ]
    have hcongr : ∀ y ∈ (C.box z δ).filter (fun y => ∀ j, y j ≡ ρY j [ZMOD (p : ℤ)]),
        pointValue sys.pts (sys.pts.map fun u => Fstar (vecOf u)) (pointList y) = Fstar y := by
      intro y hy
      have hy' : pointList y ∈ sys.pts := (henc.mem_pts _).mpr ⟨y, (Finset.mem_filter.mp hy).1, rfl⟩
      rw [pointValue_map _ sys.pts henc.nodup _ hy', hvec]
    rw [Finset.sum_congr rfl hcongr]
    simp only [hFstar]
    rw [← Int.cast_sum, hs2 p hp ρY hρ, natCast_toNat (hnonneg p hp ρY hρ)]
  cases hsol : S.solve sys with
  | none => exact absurd hsolve0 (S.complete sys hsol _)
  | some F =>
    have hF := S.sound sys F hsol
    have hlen : F.length = sys.pts.length := hF.1
    have hfun : ∀ y, (if y ∈ C.box z δ then pointValue sys.pts F (pointList y) else 0) = Fstar y := by
      intro y
      refine splitSolution_unique C H π hπ s z hz σ hσ δ hδ
        (fun y => if y ∈ C.box z δ then pointValue sys.pts F (pointList y) else 0)
        (fun y hy => by simp only [if_neg hy]) ?_ y
      intro p hp ρY hρ
      have hsum := hF.2 _ (henc.rows_complete p hp ρY hρ)
      simp only [systemRow] at hsum
      rw [hrow F hlen p hp ρY hρ] at hsum
      rw [Finset.sum_congr rfl fun y hy => if_pos (Finset.mem_filter.mp hy).1, hsum,
        natCast_toNat (hnonneg p hp ρY hρ)]
    refine ⟨F, rfl, hlen, fun f hf => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hf
    have hip : i < sys.pts.length := hlen ▸ hi
    obtain ⟨y, hy, hyu⟩ := (henc.mem_pts _).mp (List.getElem_mem hip)
    refine ⟨y, hy, ?_⟩
    have h1 := hfun y
    rw [if_pos hy, hyu, pointValue_eq_getD _ sys.pts F henc.nodup hlen,
      henc.nodup.idxOf_getElem i hip, List.getD_eq_getElem _ _ hi] at h1
    exact h1

/-- A class value of a part of the weights is below `p^e` in absolute value (the bound of `lem:residue`). -/
theorem classValueOf_natAbs_lt (H : C.ReconstructionHypotheses) (π : List Bool) (hπ : π.length ≤ C.seedLength)
    (s : Bool) (z : Fin C.ncol) (σ : Cycle.SignPattern Algorithm.traceOrder) (δ : Fin 2 → Fin (C.J + 1) → ℤ)
    (y : Fin 2 → ℤ) (p : ℕ) (hp : p ∈ C.primes) :
    (classValueOf C (splitWeight C π s) z σ δ y).natAbs ≤ p ^ C.e := by
  classical
  have hg := splitWeight_guard C H π hπ s p hp
  have habs : |classValueOf C (splitWeight C π s) z σ δ y| ≤ ∑ w, |splitWeight C π s w| := by
    unfold classValueOf
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ => ?_)
    split_ifs
    · exact le_rfl
    · simp
  have h2 : ((classValueOf C (splitWeight C π s) z σ δ y).natAbs : ℤ) ≤ ((p ^ C.e : ℕ) : ℤ) := by
    rw [Int.natCast_natAbs]
    push_cast
    have : 0 ≤ ∑ w, |splitWeight C π s w| := Finset.sum_nonneg fun w _ => abs_nonneg _
    linarith
  exact_mod_cast h2

end Entries

/-! ## The size of the answers -/

theorem ratWord_intCast_length_le (z : ℤ) {B : ℕ} (h : z.natAbs ≤ 2 ^ B) :
    (ratWord (z : ℚ)).length ≤ 2 * B + 13 := by
  unfold ratWord
  rw [List.length_append, Rat.num_intCast, Rat.den_intCast]
  have h1 := intWord_length_le z h
  have h2 : (natWord 1).length ≤ 2 * 1 + 3 := natWord_length_le_of_le (by norm_num)
  omega

/-- **The answer of every exact solver on a listed system has polynomial size** (at most `10^4 V^4`). -/
theorem solveWord_length_le_envelope (S : SolveMachine) (q : ChildRequest B1 B2) (x : SystemIndex q)
    (hx : x ∈ systemList q) :
    (solveWord (S.solve (systemAt q x))).length ≤ 10000 * envelope q ^ 4 := by
  classical
  obtain ⟨hσ, hδ, hz⟩ := mem_systemList hx
  have H : q.cellCall.ReconstructionHypotheses := reconstructionHypotheses_of_dispatch q.dispatched q.witness
  set V := envelope q with hV
  have hV1 : q.call.n + 1 ≤ V := n_succ_le_envelope q
  have hn4 : 4 ≤ q.call.n := (dispatch_admitted q.dispatched).1.1
  have hP : q.selected.1.P ≤ V := P_le_envelope q
  have he : q.cellCall.e ≤ V := e_le_envelope q
  obtain ⟨p, hp⟩ := (rules q).primes_nonempty
  have hpV : p ≤ V := (le_P_of_mem_primes q hp).trans hP
  obtain ⟨F, hsol, hlen, hent⟩ := solve_entries q.cellCall S (systemAt q x) H q.seedPrefix q.prefix_le x.1 x.2.2.2 hz
    x.2.1 hσ x.2.2.1 (by rw [digitVectors_eq]; exact hδ) (systemOf_encodes _ _ _ _ _ _)
  -- the number of entries
  have hax : ∀ j, (boxAxis q.cellCall x.2.2.2 x.2.2.1 j).length ≤ 17 * V := by
    intro j
    have h1 := (boxAxis_bounds q.cellCall x.2.2.2 x.2.2.1 j).1
    have hG := G_le_envelope q j
    omega
  have hF : F.length ≤ 17 * V * (17 * V) := by
    rw [hlen]
    show (boxPoints q.cellCall x.2.2.2 x.2.2.1).length ≤ _
    unfold boxPoints
    rw [List.length_map, List.length_product]
    exact Nat.mul_le_mul (hax 0) (hax 1)
  -- each entry
  have hpe : p ^ q.cellCall.e ≤ 2 ^ (V * V) :=
    calc p ^ q.cellCall.e ≤ (2 ^ V) ^ q.cellCall.e := Nat.pow_le_pow_left (hpV.trans (Nat.lt_two_pow_self).le) _
      _ = 2 ^ (V * q.cellCall.e) := by rw [← pow_mul]
      _ ≤ 2 ^ (V * V) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ he)
  have hentry : ∀ f ∈ F, (ratWord f).length ≤ 2 * (V * V) + 13 := by
    intro f hf
    obtain ⟨y, _, rfl⟩ := hent f hf
    exact ratWord_intCast_length_le _
      ((classValueOf_natAbs_lt q.cellCall H q.seedPrefix q.prefix_le x.1 x.2.2.2 x.2.1 x.2.2.1 y p hp).trans hpe)
  have hlist := listWord_length_le ratWord F _ hentry
  rw [hsol]
  unfold solveWord
  rw [List.length_append]
  have h1 : (natWord 1).length ≤ 2 * 1 + 3 := natWord_length_le_of_le (by norm_num)
  have hV5 : 5 ≤ V := by omega
  have hm := Nat.mul_le_mul_right (2 * (V * V) + 13) hF
  have hV4 : V ^ 3 ≤ V ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hV2 : V ^ 2 ≤ V ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  nlinarith

/-- **The exponent of the answers**: on every child, the answer of every exact solver on every listed system has
length at most `(n+1)^{e₁}`. -/
theorem solveWord_length_le (B1 B2 : ℕ) :
    ∃ e₁ : ℕ, ∀ (S : SolveMachine) (q : ChildRequest B1 B2) (x : SystemIndex q), x ∈ systemList q →
      (solveWord (S.solve (systemAt q x))).length ≤ (q.call.n + 1) ^ e₁ := by
  refine ⟨4 * (B1 + 12) + 10000 * Cells.ParameterArithmetic.preparationCoefficient B1 ^ 4,
    fun S q x hx => ?_⟩
  refine (solveWord_length_le_envelope S q x hx).trans ?_
  rw [envelope_eq, mul_pow, ← pow_mul, ← mul_assoc, mul_comm (B1 + 12) 4]
  exact pow_absorb _ _ _ (by have := (dispatch_admitted q.dispatched).1.1; omega)

/-! ## The sizes of the words between the stages

Each word between two stages of `ReconstructPhases` has length at most a polynomial in `n` times the cost of the
stages that write and read it (`printsCost`, `systemsCost`, `tablesCost`, `solvedCost`): the stage costs pay for
reading and writing their words. -/

theorem natWord_n_le_gammaWord (q : ChildRequest B1 B2) : (natWord q.call.n).length ≤ (gammaWord q).length := by
  have hc : (natWord q.call.n).length ≤ (certWord B1 B2 q.call q.witness).length := by
    unfold certWord stageWord
    rw [q.dispatched]
    simp only [List.length_cons, List.length_append, callWord]
    omega
  have hg : (certWord B1 B2 q.call q.witness).length ≤ (gammaWord q).length := by
    unfold gammaWord childInput
    simp only [List.length_append]
    omega
  omega

theorem certWord_parts (q : ChildRequest B1 B2) :
    (parametersWord q.selected.1).length + 2 * q.cellCall.ncol + 1 ≤ (certWord B1 B2 q.call q.witness).length := by
  have hb : (certifiedBits q.cellCall).length = q.cellCall.ncol := by
    unfold certifiedBits
    simp
  have hb' : (certifiedBits (runCall q.call q.selected q.witness)).length = q.cellCall.ncol := hb
  unfold certWord stageWord
  rw [q.dispatched]
  simp only [List.length_cons, List.length_append, RepairOrdinary.frame_length, hb']
  omega

theorem certWord_le_gammaWord (q : ChildRequest B1 B2) :
    (certWord B1 B2 q.call q.witness).length ≤ (gammaWord q).length := by
  unfold gammaWord childInput
  simp only [List.length_append]
  omega

theorem factorsWord_le_parametersWord (p : Cells.Parameters) :
    (listWord natWord p.factors).length ≤ (parametersWord p).length := by
  unfold parametersWord
  simp only [List.length_append]
  omega

theorem tablesPerGroup_le (q : ChildRequest B1 B2) : tablesPerGroup q ≤ q.selected.1.P ^ 3 := by
  unfold tablesPerGroup
  refine (length_flatMap_le _ _ (q.selected.1.P ^ 2) fun p hp => ?_).trans ?_
  · have hp' := (mem_primeList _ p).mp hp
    exact (residueListOf_length_le q (one_le_of_mem_primes q hp')).trans
      (Nat.pow_le_pow_left (le_P_of_mem_primes q hp') 2)
  · unfold primeList
    rw [Finset.length_sort, pow_succ' _ 2]
    exact Nat.mul_le_mul_right _ (card_primes_le q)

theorem contextWord_length_le (q : ChildRequest B1 B2) :
    (contextWord q).length ≤ 9 * (gammaWord q).length + 60 * envelope q + 60 := by
  set V := envelope q with hV
  have hV1 : q.call.n + 1 ≤ V := n_succ_le_envelope q
  have h1 := natWord_n_le_gammaWord q
  have h2 := certWord_parts q
  have h3 := certWord_le_gammaWord q
  have h4 := factorsWord_le_parametersWord q.selected.1
  have hS := scalarBounds q
  have hM : (natWord q.selected.1.M1).length ≤ 2 * V + 3 := (natWord_length_le_self _).trans (by
    have h : q.selected.1.M1 ≤ envelope q := hS.M1; omega)
  have hA : (natWord q.selected.1.A).length ≤ 2 * V + 3 := (natWord_length_le_self _).trans (by
    have h : q.selected.1.A ≤ envelope q := hS.A; omega)
  have hL : (natWord q.selected.1.Lambda).length ≤ 2 * V + 3 :=
    (natWord_length_le_self _).trans (by
      have h : q.selected.1.Lambda ≤ envelope q := hS.Lambda; omega)
  have hJ : (natWord q.cellCall.J).length ≤ 2 * V + 3 := (natWord_length_le_self _).trans (by
    have := J_le_envelope q; omega)
  have hG0 : (natWord (2 * Algorithm.traceOrder * Builder.occurrences q.call 0)).length ≤ 16 * V + 3 :=
    (natWord_length_le_self _).trans (by
      have := G_le_envelope q 0; change Builder.occurrences q.call 0 ≤ _ at this
      have e : 2 * Algorithm.traceOrder = 8 := rfl
      rw [e]; omega)
  have hG1 : (natWord (2 * Algorithm.traceOrder * Builder.occurrences q.call 1)).length ≤ 16 * V + 3 :=
    (natWord_length_le_self _).trans (by
      have := G_le_envelope q 1; change Builder.occurrences q.call 1 ≤ _ at this
      have e : 2 * Algorithm.traceOrder = 8 := rfl
      rw [e]; omega)
  have hpair : (bitWord (decide (q.call.kind = .pair))).length ≤ 5 :=
    natWord_length_le_of_le (B := 1) (by split <;> norm_num)
  have hcol : (natWord q.cellCall.ncol).length ≤ 2 * V + 3 := by
    apply natWord_length_le_of_le
    show 2 ^ (q.call.n - q.selected.1.k) ≤ 2 ^ V
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have htg : (natWord (tablesPerGroup q)).length ≤ 2 * (3 * V) + 3 := by
    apply natWord_length_le_of_le
    calc tablesPerGroup q ≤ q.selected.1.P ^ 3 := tablesPerGroup_le q
      _ ≤ (2 ^ V) ^ 3 := Nat.pow_le_pow_left ((P_le_envelope q).trans (Nat.lt_two_pow_self).le) 3
      _ = 2 ^ (3 * V) := by rw [← pow_mul, mul_comm]
  have hbits := listWord_length_le bitWord (certifiedBits q.cellCall) 5
    (fun b _ => natWord_length_le_of_le (B := 1) (by split <;> norm_num))
  have hb : (certifiedBits q.cellCall).length = q.cellCall.ncol := by
    unfold certifiedBits
    simp
  rw [hb] at hbits
  unfold contextWord
  simp only [List.length_append]
  omega

/-- **The print inputs fit the cost of `prints`.** -/
theorem printsWord_length_le (q : ChildRequest B1 B2) :
    (printsWord q).length ≤ (130 * envelope q + 200) * printsCost q := by
  have hctx := contextWord_length_le q
  have hV1 : q.call.n + 1 ≤ envelope q := n_succ_le_envelope q
  have hitem : ∀ r ∈ printList q, (RepairOrdinary.frame (printIndexWord r) ++ RepairOrdinary.frame (printInput r)).length ≤
      4 * ((prepWord B1 B2 q.call q.witness).length + (gammaTableWord q).length + (q.call.n + 1) ^ sizeExp B1 B2) + 2 := by
    intro r hr
    have hi := printIndexWord_le_sizeExp hr
    obtain ⟨s, σ, δ, p, ρ, -, -, rfl⟩ := mem_printList hr
    simp only [List.length_append, RepairOrdinary.frame_length, printInput, printRequestOf] at hi ⊢
    omega
  have hl := listWord_length_le _ _ _ hitem
  have hT := printList_length_le q
  unfold printsWord printsCost
  rw [List.length_append, RepairOrdinary.frame_length]
  have hm := Nat.mul_le_mul_right (4 * ((prepWord B1 B2 q.call q.witness).length + (gammaTableWord q).length +
    (q.call.n + 1) ^ sizeExp B1 B2) + 2) hT
  have hE : 1 ≤ (q.call.n + 1) ^ sizeExp B1 B2 := Nat.one_le_pow _ _ (by omega)
  have hTX : tableCount q ≤ tableCount q * ((prepWord B1 B2 q.call q.witness).length + (gammaTableWord q).length +
    (q.call.n + 1) ^ sizeExp B1 B2) := Nat.le_mul_of_pos_right _ (by omega)
  nlinarith

/-- **The printed tables fit the costs of `tables` and `systems`.** -/
theorem tablesWord_length_le (q : ChildRequest B1 B2) :
    (tablesWord q).length ≤ (8 * envelope q ^ 2 + 60 * envelope q + 140) *
      (tableCount q * (q.cellCall.ncol + (q.call.n + 1) ^ sizeExp B1 B2) + (gammaWord q).length + 1) := by
  classical
  set V := envelope q with hV
  have hctx := contextWord_length_le q
  have hP : q.selected.1.P ≤ V := P_le_envelope q
  have he : q.cellCall.e ≤ V := e_le_envelope q
  have hitem : ∀ r ∈ printList q, (printIndexWord r ++
      listWord NearCubicGates.Close.Interfaces.intWord (printTable r)).length ≤
        (8 * V ^ 2 + 64) * (q.cellCall.ncol + (q.call.n + 1) ^ sizeExp B1 B2) := by
    intro r hr
    have hi := printIndexWord_le_sizeExp hr
    obtain ⟨s, σ, δ, p, ρ, -, -, hrq⟩ := mem_printList hr
    have hp : p.1 ∈ q.cellCall.primes := (mem_primeList _ _).mp p.2
    have hpV : r.prime ≤ V := by rw [hrq]; exact (le_P_of_mem_primes q hp).trans hP
    have hpr : r.prime ∈ r.child.cellCall.primes := r.prime_mem
    have he' : r.child.cellCall.e ≤ V := by rw [hrq]; exact he
    have hn' : r.child.call.n = q.call.n := by rw [hrq]; rfl
    have hncol : r.child.cellCall.ncol = q.cellCall.ncol := by rw [hrq]; rfl
    have hentry : ∀ y ∈ printTable r, (NearCubicGates.Close.Interfaces.intWord y).length ≤ 2 * (V * V) + 8 := by
      intro y hy
      unfold printTable at hy
      obtain ⟨z, rfl⟩ := List.mem_ofFn.mp hy
      apply intWord_length_le
      have hQ : (0 : ℤ) < (r.prime : ℤ) ^ r.child.cellCall.e := by
        have : 1 ≤ r.prime := by rw [hrq]; exact one_le_of_mem_primes q hp
        positivity
      have h1 := centeredResidue_natAbs_le ((r.prime : ℤ) ^ r.child.cellCall.e)
        (printedCountOf r.child.cellCall (splitWeight r.child.cellCall r.child.seedPrefix r.sign) z r.pattern r.prime
          r.digits r.residues) hQ
      have h2 : ((r.prime : ℤ) ^ r.child.cellCall.e).toNat = r.prime ^ r.child.cellCall.e := by
        rw [← Int.natCast_pow, Int.toNat_natCast]
      have h3 : r.prime ^ r.child.cellCall.e ≤ 2 ^ (V * V) :=
        calc r.prime ^ r.child.cellCall.e ≤ (2 ^ V) ^ r.child.cellCall.e :=
              Nat.pow_le_pow_left (hpV.trans (Nat.lt_two_pow_self).le) _
          _ = 2 ^ (V * r.child.cellCall.e) := by rw [← pow_mul]
          _ ≤ 2 ^ (V * V) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ he')
      rw [h2] at h1
      exact h1.trans h3
    have hl := listWord_length_le _ _ _ hentry
    have hlen : (printTable r).length = q.cellCall.ncol := by
      rw [← hncol]
      simp [printTable]
    rw [hlen] at hl
    rw [hn'] at hi
    simp only [List.length_append]
    have hVV : V * V = V ^ 2 := by ring
    rw [hVV] at hl
    have hE : 1 ≤ (q.call.n + 1) ^ sizeExp B1 B2 := Nat.one_le_pow _ _ (by omega)
    nlinarith
  have hl := listWord_length_le _ _ _ hitem
  have hT := printList_length_le q
  unfold tablesWord
  rw [List.length_append]
  have hm := Nat.mul_le_mul_right ((8 * V ^ 2 + 64) * (q.cellCall.ncol + (q.call.n + 1) ^ sizeExp B1 B2)) hT
  have hE : 1 ≤ (q.call.n + 1) ^ sizeExp B1 B2 := Nat.one_le_pow _ _ (by omega)
  have hTE : tableCount q ≤ tableCount q * (q.cellCall.ncol + (q.call.n + 1) ^ sizeExp B1 B2) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hV0 : 0 ≤ V ^ 2 := Nat.zero_le _
  have hV1 : q.call.n + 1 ≤ V := n_succ_le_envelope q
  have hVV2 : V ≤ V ^ 2 := by nlinarith
  nlinarith

/-- **The systems fit the costs of `systems` and `solved`.** -/
theorem systemsWord_length_le (q : ChildRequest B1 B2) :
    (systemsWord q).length ≤ (10 ^ 6 * envelope q ^ 5 + 4) * (systemCount q + (gammaWord q).length + 1) := by
  set V := envelope q with hV
  have hV1 : q.call.n + 1 ≤ V := n_succ_le_envelope q
  have hn := natWord_n_le_gammaWord q
  have hitem : ∀ x ∈ systemList q, (RepairOrdinary.frame (systemTag q x) ++
      RepairOrdinary.frame (Formats.sysWord (systemAt q x))).length ≤ 10 ^ 6 * V ^ 5 := by
    intro x hx
    have hs : (Formats.sysWord (systemAt q x)).length ≤ 100000 * V ^ 5 :=
      sysWord_length_le_envelope q q.seedPrefix x.1 x.2.2.2 x.2.1 x.2.2.1
    have hax : ∀ j, (boxAxis q.cellCall x.2.2.2 x.2.2.1 j).length ≤ 17 * V := by
      intro j
      have h1 := (boxAxis_bounds q.cellCall x.2.2.2 x.2.2.1 j).1
      have hG := G_le_envelope q j
      omega
    have hpts : (systemAt q x).pts.idxOf [0, 0] ≤ 17 * V * (17 * V) := by
      refine (List.idxOf_le_length).trans ?_
      show (boxPoints q.cellCall x.2.2.2 x.2.2.1).length ≤ _
      unfold boxPoints
      rw [List.length_map, List.length_product]
      exact Nat.mul_le_mul (hax 0) (hax 1)
    have hk : |Cycle.kappa Algorithm.traceOrder x.2.1| ≤ 2 := by
      unfold Cycle.kappa
      have hp : |∏ l, Cycle.signValue (x.2.1 l)| = 1 := by
        rw [Finset.abs_prod]
        simp [Cycle.abs_signValue]
      calc |1 + (-1 : ℤ) ^ Algorithm.traceOrder * ∏ l, Cycle.signValue (x.2.1 l)|
          ≤ |(1 : ℤ)| + |(-1 : ℤ) ^ Algorithm.traceOrder * ∏ l, Cycle.signValue (x.2.1 l)| := abs_add_le _ _
        _ = 2 := by rw [abs_mul, hp]; norm_num
    have hcoef : (systemCoef q x).natAbs ≤ 2 ^ 2 := by
      have h : |systemCoef q x| ≤ 2 := by
        unfold systemCoef partSign
        rw [abs_mul]
        split <;> simp [hk]
      have : ((systemCoef q x).natAbs : ℤ) ≤ 4 := by
        rw [Int.natCast_natAbs]
        linarith
      exact_mod_cast this
    have htag : (systemTag q x).length ≤ 2 * 2 + 8 + (2 * (17 * V * (17 * V)) + 3) := by
      unfold systemTag
      rw [List.length_append]
      have h1 := intWord_length_le (systemCoef q x) hcoef
      have h2 := natWord_length_le_self ((systemAt q x).pts.idxOf [0, 0])
      omega
    simp only [List.length_append, RepairOrdinary.frame_length]
    have hV5 : 1 ≤ V ^ 5 := Nat.one_le_pow _ _ (by omega)
    have hV2 : V ^ 2 ≤ V ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
    nlinarith
  have hl := listWord_length_le _ _ _ hitem
  have hS := systemList_length_le q
  unfold systemsWord
  rw [List.length_append, RepairOrdinary.frame_length]
  have hm := Nat.mul_le_mul_right (10 ^ 6 * V ^ 5) hS
  have hV5 : 1 ≤ V ^ 5 := Nat.one_le_pow _ _ (by omega)
  have hSV : systemCount q ≤ systemCount q * V ^ 5 := Nat.le_mul_of_pos_right _ (by omega)
  have hγV : (gammaWord q).length ≤ (gammaWord q).length * V ^ 5 := Nat.le_mul_of_pos_right _ (by omega)
  nlinarith

/-- The tag of a listed system has length at most `578 V^2 + 15`. -/
theorem systemTag_length_le (q : ChildRequest B1 B2) (x : SystemIndex q) :
    (systemTag q x).length ≤ 2 * 2 + 8 + (2 * (17 * envelope q * (17 * envelope q)) + 3) := by
  set V := envelope q with hV
  have hV1 : q.call.n + 1 ≤ V := n_succ_le_envelope q
  have hax : ∀ j, (boxAxis q.cellCall x.2.2.2 x.2.2.1 j).length ≤ 17 * V := by
    intro j
    have h1 := (boxAxis_bounds q.cellCall x.2.2.2 x.2.2.1 j).1
    have hG := G_le_envelope q j
    omega
  have hpts : (systemAt q x).pts.idxOf [0, 0] ≤ 17 * V * (17 * V) := by
    refine (List.idxOf_le_length).trans ?_
    show (boxPoints q.cellCall x.2.2.2 x.2.2.1).length ≤ _
    unfold boxPoints
    rw [List.length_map, List.length_product]
    exact Nat.mul_le_mul (hax 0) (hax 1)
  have hk : |Cycle.kappa Algorithm.traceOrder x.2.1| ≤ 2 := by
    unfold Cycle.kappa
    have hp : |∏ l, Cycle.signValue (x.2.1 l)| = 1 := by
      rw [Finset.abs_prod]
      simp [Cycle.abs_signValue]
    calc |1 + (-1 : ℤ) ^ Algorithm.traceOrder * ∏ l, Cycle.signValue (x.2.1 l)|
        ≤ |(1 : ℤ)| + |(-1 : ℤ) ^ Algorithm.traceOrder * ∏ l, Cycle.signValue (x.2.1 l)| := abs_add_le _ _
      _ = 2 := by rw [abs_mul, hp]; norm_num
  have hcoef : (systemCoef q x).natAbs ≤ 2 ^ 2 := by
    have h : |systemCoef q x| ≤ 2 := by
      unfold systemCoef partSign
      rw [abs_mul]
      split <;> simp [hk]
    have : ((systemCoef q x).natAbs : ℤ) ≤ 4 := by
      rw [Int.natCast_natAbs]
      linarith
    exact_mod_cast this
  unfold systemTag
  rw [List.length_append]
  have h1 := intWord_length_le (systemCoef q x) hcoef
  have h2 := natWord_length_le_self ((systemAt q x).pts.idxOf [0, 0])
  omega

/-- **The answers fit the costs of `solved` and `total`.** -/
theorem solvedWord_length_le (S : SolveMachine) (q : ChildRequest B1 B2) :
    (solvedWord q S).length ≤ (10 ^ 5 * envelope q ^ 4 + 4) * (systemCount q + (gammaWord q).length + 1) := by
  set V := envelope q with hV
  have hV1 : q.call.n + 1 ≤ V := n_succ_le_envelope q
  have hn := natWord_n_le_gammaWord q
  have hitem : ∀ x ∈ systemList q, (systemTag q x ++
      solveWord (S.solve (systemAt q x))).length ≤ 10 ^ 5 * V ^ 4 := by
    intro x hx
    have hs : (solveWord (S.solve (systemAt q x))).length ≤ 10000 * V ^ 4 := solveWord_length_le_envelope S q x hx
    have htag := systemTag_length_le q x
    simp only [List.length_append]
    have hV4 : 1 ≤ V ^ 4 := Nat.one_le_pow _ _ (by omega)
    have hV2 : V ^ 2 ≤ V ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    rw [← hV] at htag
    nlinarith
  have hl := listWord_length_le _ _ _ hitem
  have hS := systemList_length_le q
  unfold solvedWord
  rw [List.length_append]
  have hm := Nat.mul_le_mul_right (10 ^ 5 * V ^ 4) hS
  have hV4 : 1 ≤ V ^ 4 := Nat.one_le_pow _ _ (by omega)
  nlinarith

end NearQuarticWires.Reconstruct
