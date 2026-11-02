import Proof.Quartic.Control.GammaRun
import Proof.Foundations.OrdinaryRewindCarrier

/-!
# The coefficient stage of a child evaluation

Paper: Step 3 of `sec:algorithm`, paper/paper.tex; `cor:conditional`; `prop:time`. The request of the walk of index `i` is `Greedy.gammaRequest` of the `i`-th walk of `Greedy.walkList`
(`walkReq`, `walkReq_word`), and the table written by `gammaP` is the coefficient table `Greedy.gammaTable`
(`tableWord_eq`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearQuarticWires.Control

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.RepairOrdinary.Streaming (marks marks_length marks_append)
open NearCubicGates.Close.Interfaces (Call listWord)
open NearQuarticWires.Greedy

/-- **A word function writes at most one cell more than its budget.** -/
theorem output_length_le {Request : Type} {input output : Request → List Bool} {budget : Request → ℕ}
    (f : WordFunction Request input output budget) (r : Request) : (output r).length ≤ budget r + 1 := by
  obtain ⟨receipt, hrun, hout⟩ := f.realizes r
  have h1 := (NearCubicGates.Close.WorkerArith.runFrom_len f.program.machine f.program.outputTape (budget r) _ 0
    receipt hrun (by simp [initialConfiguration])
    (by simp [initialConfiguration, Program.inputTapes, f.program.outputFresh])).2
  have h2 := NearCubicWires.RepairOrdinary.runFrom_steps_le _ _ _ _ hrun
  rw [← hout]; omega

theorem walkDigits_mod (kh : ℕ) : ∀ m i, walkDigits kh m i = walkDigits kh m (i % 2 ^ (kh * m))
  | 0, _ => rfl
  | m + 1, i => by
    simp only [walkDigits]
    congr 1
    · exact (Nat.mod_mod_of_dvd i (pow_dvd_pow 2 (by nlinarith))).symm
    · rw [walkDigits_mod kh m (i / 2 ^ kh), walkDigits_mod kh m (i % 2 ^ (kh * (m + 1)) / 2 ^ kh)]
      congr 1
      rw [show kh * (m + 1) = kh + kh * m by ring, pow_add, Nat.mod_mul_right_div_self, Nat.mod_mod]

variable {B1 B2 : ℕ}

theorem walkList_len (q : ChildRequest B1 B2) :
    (walkList q.cellCall.seed.N).length = 2 ^ (q.cellCall.seed.kh * 8) := by
  rw [walkList_length]
  simp [Algorithm.traceOrder, ← pow_mul]

theorem walkList_len_pos (q : ChildRequest B1 B2) : 0 < (walkList q.cellCall.seed.N).length := by
  rw [walkList_len]; positivity

/-- The request of the walk of index `i` (indices taken modulo the number of walks). -/
noncomputable def walkReq (q : ChildRequest B1 B2) (i : ℕ) : Machine.GammaRequest :=
  gammaRequest q ((walkList q.cellCall.seed.N)[i % (walkList q.cellCall.seed.N).length]'(Nat.mod_lt _
    (walkList_len_pos q)))

theorem requestHead_eq (q : ChildRequest B1 B2) :
    requestHead q = headWord q.cellCall.seed.ell q.cellCall.seed.kh q.cellCall.seed.Q q.seedPrefix := by
  simp [requestHead, headWord, seedWord, List.append_assoc]

/-- **The request word of the walk of index `i`.** -/
theorem walkReq_word (q : ChildRequest B1 B2) (i : ℕ) :
    Machine.gammaRequestWord (walkReq q i) = headWord q.cellCall.seed.ell q.cellCall.seed.kh q.cellCall.seed.Q
      q.seedPrefix ++ natWord 8 ++ (walkDigits q.cellCall.seed.kh 8 i).flatMap natWord := by
  rw [walkReq, gammaRequestWord_walk, requestHead_eq, walkDigits_mod _ 8 i, walkList_len]

/-- **The table word is the coefficient table.** -/
theorem tableWord_eq (q : ChildRequest B1 B2) :
    tableWord q.cellCall.seed.kh (fun i => Machine.gammaTarget (walkReq q i)) =
      listWord NearCubicGates.Close.Interfaces.intWord (gammaTable q) := by
  have hlen : (gammaTable q).length = 2 ^ (8 * q.cellCall.seed.kh) := by
    rw [gammaTable, List.length_map, walkList_len, Nat.mul_comm]
  have hmap : (List.range (2 ^ (8 * q.cellCall.seed.kh))).map (fun i => Machine.gammaTarget (walkReq q i)) =
      gammaTable q := by
    apply List.ext_getElem (by simp [hlen])
    intro n h1 h2
    have hn : n < (walkList q.cellCall.seed.N).length := by
      rw [walkList_len, Nat.mul_comm]; simpa using h1
    simp only [List.getElem_map, List.getElem_range, gammaTable, walkReq, gammaTarget_gammaRequest]
    congr 2
    exact Nat.mod_eq_of_lt hn
  rw [tableWord, listWord, hlen, ← hmap, List.flatMap_map]


theorem seed_kh (q : ChildRequest B1 B2) : q.cellCall.seed.kh = q.selected.1.k / 2 := rfl
theorem seed_ell (q : ChildRequest B1 B2) : q.cellCall.seed.ell = q.selected.1.ellf := rfl
theorem seed_Q (q : ChildRequest B1 B2) : q.cellCall.seed.Q = q.selected.1.Q := rfl

theorem digits_length_le (kh : ℕ) : ∀ ds : List ℕ, (∀ d ∈ ds, d < 2 ^ kh) →
    (ds.flatMap natWord).length ≤ ds.length * (2 * kh + 3)
  | [], _ => by simp
  | d :: ds, h => by
    have h1 := natWord_length_le_field kh d (h d (by simp))
    have h2 := digits_length_le kh ds (fun x hx => h x (by simp [hx]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    nlinarith

/-- The bound on the length of the requests. -/
def reqLen (ell kh Q : ℕ) (π : List Bool) : ℕ := (headWord ell kh Q π).length + 9 + 8 * (2 * kh + 3)

theorem walkReq_length (q : ChildRequest B1 B2) (i : ℕ) :
    (Machine.gammaRequestWord (walkReq q i)).length ≤
      reqLen q.cellCall.seed.ell q.cellCall.seed.kh q.cellCall.seed.Q q.seedPrefix := by
  rw [walkReq_word]
  have h8 : (natWord 8).length = 9 := by
    rw [NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length]; simp [natBitLength]; decide
  have hd := digits_length_le q.cellCall.seed.kh (walkDigits q.cellCall.seed.kh 8 i) (walkDigits_lt _ _ _)
  rw [walkDigits_length] at hd
  simp only [List.length_append, h8]
  unfold reqLen; omega

/-- The register capacity on a child evaluation. -/
noncomputable def gammaCap (q : ChildRequest B1 B2) (B : ℕ) : ℕ :=
  10000 * (2 ^ ((childInput q).length + 2) + (listWord NearCubicGates.Close.Interfaces.intWord (gammaTable q)).length +
    B + 10)

/-- The words of a child evaluation that `gammaP` reads, in the order of `gammaCost`. -/
noncomputable def gammaRunCost (q : ChildRequest B1 B2) (B : ℕ) : ℕ :=
  gammaCost q.call (params6 q.selected.1) (params10 q.selected.1)
    ((StageLift.parameterHeadScalars q.selected.1).drop 19) (q.selected.1.primes.sort (· ≤ ·))
    (StageLift.parameterTailScalars q.selected.1) q.selected.1.factors q.selected.1.k q.selected.1.Q q.selected.1.ellf
    (Program.witnessPrefix q.call q.selected.1 q.witness)
    (Program.certifiedBits (Program.runCall q.call q.selected q.witness)) q.seedPrefix (childInput q)
    (reqLen q.selected.1.ellf (q.selected.1.k / 2) q.selected.1.Q q.seedPrefix) B
    (listWord NearCubicGates.Close.Interfaces.intWord (gammaTable q)).length


theorem lt_two_pow_of_natWord (x : ℕ) (L : ℕ) (h : (natWord x).length ≤ L) : x < 2 ^ L := by
  have h1 : x < 2 ^ natBitLength x := Nat.lt_pow_succ_log_self (by norm_num) x
  have h2 := natBitLength_le_natWord x
  exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- **The coefficient stage of a child evaluation.** For every word function computing one coefficient within
budget at most `B` on the requests of the child, the program `gammaP` writes exactly `frame (gammaWord q)`. -/
theorem gammaRun_exec {gammaBudget : Machine.GammaRequest → ℕ}
    (f : WordFunction Machine.GammaRequest Machine.gammaRequestWord
      (fun r => NearCubicGates.Close.Interfaces.intWord (Machine.gammaTarget r)) gammaBudget)
    (q : ChildRequest B1 B2) (B : ℕ) (hB : ∀ w, gammaBudget (gammaRequest q w) ≤ B) :
    ∃ τ, WXExec (gammaCap q B) (gammaP f.program) (gammaStart _ (childInput q)) τ (gammaRunCost q B) ∧
      τ.st (cOUT _) = frame (gammaWord q) := by
  have hw := childInput_fields q
  have hl := congrArg List.length hw
  simp only [seedPre, tailWord, List.length_append, List.length_cons, List.length_nil] at hl
  have hcapeq : gammaCap q B = 10000 * (2 ^ ((childInput q).length + 2) +
      (listWord NearCubicGates.Close.Interfaces.intWord (gammaTable q)).length + B + 10) := rfl
  have hwpow : (childInput q).length < 2 ^ (childInput q).length := Nat.lt_two_pow_self
  have hp4 : 2 ^ (childInput q).length * 4 = 2 ^ ((childInput q).length + 2) := by rw [pow_add]; norm_num
  have hpow : ∀ a, a ≤ (childInput q).length + 2 → 2 ^ a ≤ gammaCap q B := fun a ha => by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) ha; omega
  have hk : q.selected.1.k < 2 ^ (childInput q).length := lt_two_pow_of_natWord _ _ (by omega)
  have hkh : (natWord (q.selected.1.k / 2)).length ≤ (natWord q.selected.1.k).length := by
    rw [NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length,
      NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length]
    have := natBitLength_mono (show q.selected.1.k / 2 ≤ q.selected.1.k by omega); omega
  have hsw : (seedWord q.selected.1.ellf (q.selected.1.k / 2) q.selected.1.Q).length ≤ 3 * (childInput q).length := by
    simp only [seedWord, List.length_append]; omega
  have hπ : q.seedPrefix.length ≤ (childInput q).length := by
    have : (frame q.seedPrefix).length = 2 * q.seedPrefix.length + 1 := by
      rw [NearCubicGates.Close.Codec.frame_eq_marks]; simp [marks_length]
    omega
  have hhw : (headWord q.selected.1.ellf (q.selected.1.k / 2) q.selected.1.Q q.seedPrefix).length ≤
      3 * (childInput q).length + 4 * q.seedPrefix.length + 6 := by
    have h1 := NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length q.seedPrefix.length
    have h2 := NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length
      (Algorithm.CellCall.prefixValue q.seedPrefix)
    have h3 := natBitLength_le_self_succ q.seedPrefix.length
    have h4 := natBitLength_le_of_lt_pow (E := q.seedPrefix.length + 1) (by omega)
      (lt_trans (Greedy.prefixValue_lt q.seedPrefix) (Nat.pow_lt_pow_right (by norm_num) (by omega)))
    simp only [headWord, List.length_append]; omega
  have hlist : ∀ xs : List ℕ, (listWord natWord xs).length ≤ (childInput q).length → ListFits (gammaCap q B) xs :=
    fun xs h => ⟨hpow _ (by have := (listWord_count natWord xs natWord_pos).1; omega),
      by have := (listWord_count natWord xs natWord_pos).2; omega,
      fun x hx => by have := listWord_elem natWord xs x hx; have := natBitLength_le_natWord x; omega⟩
  have hnats : ∀ xs : List ℕ, (xs.flatMap natWord).length ≤ (childInput q).length →
      ∀ x ∈ xs, natBitLength x + 1 ≤ gammaCap q B :=
    fun xs h x hx => by have := length_le_flatMap natWord xs x hx; have := natBitLength_le_natWord x; omega
  have hnk := natBitLength_le_natWord q.selected.1.k
  have htab := tableWord_eq q
  rw [seed_kh] at htab
  have hU := congrArg List.length htab
  obtain ⟨τ, e, hout⟩ := gammaP_exec f (gammaCap q B) (childInput q) q.call (params6 q.selected.1) (params10 q.selected.1)
    ((StageLift.parameterHeadScalars q.selected.1).drop 19) (q.selected.1.primes.sort (· ≤ ·)) (StageLift.parameterTailScalars q.selected.1)
    q.selected.1.factors q.selected.1.k q.selected.1.Q q.selected.1.ellf (Program.witnessPrefix q.call q.selected.1 q.witness)
    (Program.certifiedBits (Program.runCall q.call q.selected q.witness)) q.seedPrefix hw rfl rfl
    (by simp [StageLift.parameterHeadScalars_length]) (StageLift.parameterTailScalars_length q.selected.1)
    (readFits_of_le _ _ _ _ (hpow _ (by omega))) (hnats _ (by omega)) (hnats _ (by omega)) (hnats _ (by omega))
    (hlist _ (by omega)) (hlist _ (by omega)) (by omega) (by omega) (by omega) (by omega)
    (walkReq q) (fun i => by rw [walkReq_word, seed_ell, seed_kh, seed_Q]) B
    (reqLen q.selected.1.ellf (q.selected.1.k / 2) q.selected.1.Q q.seedPrefix)
    (fun i => hB _) (fun i => walkReq_length q i) (by omega) (by rw [hU]; omega)
  rw [hU] at e
  refine ⟨τ, e, ?_⟩
  rw [hout, htab]
  rfl

end NearQuarticWires.Control
