import Proof.Quartic.Reconstruct.GatherProgLinkOut

/-!
# The gathering program: the sizes of the numbers of a child

Paper: `prop:time`, paper/paper.tex.

Every number read by the gathering has at most `ℓ = 100 (V+1)^2` bits (`ellQ`), `V` the envelope of the child: the
index numbers of a table because its index word has length at most `100 V^2`
(`printIndexWord_length_le_envelope`), the entries because they are residues modulo `p^e ≤ 2^{V·V}`
(`entry_natAbs_le`). The records of a group stay below `2^{V^2 + 8V + 1}` (`grp_W_le`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearQuarticWires.Reconstruct.GatherProg

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces (listWord bitWord)
open NearQuarticWires.Greedy NearQuarticWires.Program
open NearQuarticWires.Reconstruct

variable {B1 B2 : ℕ}

/-- The bit bound of the numbers of the gathering. -/
noncomputable def ellQ (q : ChildRequest B1 B2) : ℕ := 100 * (envelope q + 1) ^ 2

theorem nbl_mem_flatMap (L : List ℕ) (v : ℕ) (hv : v ∈ L) : 2 * natBitLength v + 1 ≤ (L.flatMap natWord).length := by
  rw [← natWord_length]
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hv
  simp only [List.flatMap_append, List.flatMap_cons, List.length_append]
  omega

theorem nbl_le_of_le_pow {v k : ℕ} (hv : v ≤ 2 ^ k) : natBitLength v ≤ k + 1 :=
  natBitLength_le_of_lt_two_pow (lt_of_le_of_lt hv (Nat.pow_lt_pow_right (by norm_num) (by omega))) (by omega)

theorem mem_groupList_digits (q : ChildRequest B1 B2) (G : Grp q) (hG : G ∈ groupList q) : G.2.2 ∈ digitList q := by
  unfold groupList at hG
  simp only [List.mem_flatMap, List.mem_map] at hG
  obtain ⟨s, -, σ, -, δ, hδ, rfl⟩ := hG
  exact hδ

/-- The entries of a printed table are at most `2^{V·V}` in absolute value. -/
theorem entry_natAbs_le (q : ChildRequest B1 B2) (G : Grp q) (pr : {p // p ∈ primeList q.cellCall} × (Fin 2 → ℤ)) :
    ∀ e ∈ printTable (tableAt q G pr), e.natAbs ≤ 2 ^ (envelope q * envelope q) := by
  intro y hy
  set V := envelope q
  have hp : pr.1.1 ∈ q.cellCall.primes := (mem_primeList _ _).mp pr.1.2
  have hpV : pr.1.1 ≤ V := (le_P_of_mem_primes q hp).trans (P_le_envelope q)
  have he : q.cellCall.e ≤ V := e_le_envelope q
  unfold printTable at hy
  obtain ⟨z, rfl⟩ := List.mem_ofFn.mp hy
  have hQ : (0 : ℤ) < (pr.1.1 : ℤ) ^ q.cellCall.e := by
    have : 1 ≤ pr.1.1 := one_le_of_mem_primes q hp
    positivity
  have h1 := centeredResidue_natAbs_le ((pr.1.1 : ℤ) ^ q.cellCall.e)
    (printedCountOf q.cellCall (splitWeight q.cellCall q.seedPrefix G.1) z G.2.1 pr.1.1 G.2.2 pr.2) hQ
  have h2 : ((pr.1.1 : ℤ) ^ q.cellCall.e).toNat = pr.1.1 ^ q.cellCall.e := by
    rw [← Int.natCast_pow, Int.toNat_natCast]
  have h3 : pr.1.1 ^ q.cellCall.e ≤ 2 ^ (V * V) :=
    calc pr.1.1 ^ q.cellCall.e ≤ (2 ^ V) ^ q.cellCall.e :=
          Nat.pow_le_pow_left (hpV.trans (Nat.lt_two_pow_self).le) _
      _ = 2 ^ (V * q.cellCall.e) := by rw [← pow_mul]
      _ ≤ 2 ^ (V * V) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ he)
  rw [h2] at h1
  exact h1.trans h3

/-- The index numbers of a table. -/
def idxN (d : TblD) : List ℕ :=
  [d.s, d.pat.length] ++ d.pat ++ [d.p, d.dl.length] ++ d.dl.flatMap intNats ++ [2] ++ intNats d.r0 ++ intNats d.r1

theorem tblNats_split (d : TblD) : tblNats d = idxN d ++ (d.ents.length :: d.ents.flatMap intNats) := by
  simp [tblNats, idxN]

theorem idxN_word (q : ChildRequest B1 B2) (G : Grp q) (pr : {p // p ∈ primeList q.cellCall} × (Fin 2 → ℤ)) :
    (idxN ((grpD q G).tbl (rowD q G pr))).flatMap natWord = printIndexWord (tableAt q G pr) := by
  have h := tableItemWord_eq q G pr
  rw [tblNats_split, List.flatMap_append] at h
  unfold tableItemWord at h
  rw [listWord_int] at h
  exact (List.append_cancel_right h).symm

theorem ellQ_ge (q : ChildRequest B1 B2) : 2 * emitExp q + 10 ≤ ellQ q ∧ 50 * envelope q ^ 2 ≤ ellQ q ∧
    envelope q * envelope q + 1 ≤ ellQ q ∧ envelope q + 1 ≤ ellQ q := by
  unfold ellQ emitExp
  have h1 : envelope q ^ 2 ≤ (envelope q + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h2 : envelope q * envelope q = envelope q ^ 2 := by ring
  have h3 : (envelope q + 1) ^ 2 = envelope q ^ 2 + 2 * envelope q + 1 := by ring
  refine ⟨by nlinarith, by omega, by omega, by omega⟩

/-- **The numbers of a group have at most `ℓ` bits.** -/
theorem grpD_nats_bits (q : ChildRequest B1 B2) (G : Grp q) (hG : G ∈ groupList q) :
    ∀ v ∈ (grpD q G).nats, natBitLength v ≤ ellQ q := by
  classical
  obtain ⟨e1, e2, e3, e4⟩ := ellQ_ge q
  intro v hv
  unfold GrpD.nats at hv
  obtain ⟨r, hr, hv⟩ := List.mem_flatMap.mp hv
  simp only [grpD, List.mem_map] at hr
  obtain ⟨pr, hpr, rfl⟩ := hr
  rw [tblNats_split] at hv
  rcases List.mem_append.mp hv with hv | hv
  · have h1 := nbl_mem_flatMap _ v hv
    rw [idxN_word] at h1
    have hδ : G.2.2 ∈ digitSet q := (mem_digitList q G.2.2).mp (mem_groupList_digits q G hG)
    have hρ : pr.2 ∈ residueSet q pr.1.1 := mem_residueListOf (mem_rowList q pr hpr)
    have h2 := printIndexWord_length_le_envelope (tableAt q G pr) (tableAt q G pr).prime_mem hδ hρ
    have h3 : (tableAt q G pr).child = q := rfl
    rw [h3] at h2
    omega
  · rcases List.mem_cons.mp hv with h | h
    · rw [h]
      have : ((grpD q G).tbl (rowD q G pr)).ents.length = q.cellCall.ncol := printTable_length _
      rw [this]
      have h1 : natBitLength q.cellCall.ncol ≤ q.call.n - q.selected.1.k + 1 := nbl_le_of_le_pow le_rfl
      have := n_succ_le_envelope q
      omega
    · obtain ⟨y, hy, hv⟩ := List.mem_flatMap.mp h
      have hyb := entry_natAbs_le q G pr y hy
      simp only [intNats, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · split_ifs <;> simp [natBitLength] <;> omega
      · have := nbl_le_of_le_pow hyb; omega

theorem mem_cnts {ents : List ℤ} {bits : List ℕ} {x : ℕ} (hx : x ∈ cnts ents bits) : ∃ e ∈ ents, x = e.toNat := by
  unfold cnts at hx
  obtain ⟨⟨e, b⟩, hm, h⟩ := List.mem_filterMap.mp hx
  split_ifs at h with hb
  · simp only [Option.some.injEq] at h
    exact ⟨e, (List.of_mem_zip hm).1, h.symm⟩

/-- **The certified counts of a group** are at most `2^{V·V}`. -/
theorem cfOf_le (q : ChildRequest B1 B2) (G : Grp q) :
    ∀ x ∈ cfOf (grpD q G) (certNats q), x ≤ 2 ^ (envelope q * envelope q) := by
  intro x hx
  unfold cfOf at hx
  obtain ⟨r, hr, hx⟩ := List.mem_flatMap.mp hx
  simp only [grpD, List.mem_map] at hr
  obtain ⟨pr, -, rfl⟩ := hr
  obtain ⟨e, he, rfl⟩ := mem_cnts hx
  have := entry_natAbs_le q G pr e he
  omega

end NearQuarticWires.Reconstruct.GatherProg
