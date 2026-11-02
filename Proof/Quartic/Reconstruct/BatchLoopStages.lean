import Proof.Quartic.Reconstruct.BatchLoopTables
import Proof.Quartic.Reconstruct.Answers
import Proof.Quartic.Control.GammaControl

/-!
# The stage `tables` of the reconstruction

Paper: `lem:print`(a), paper/paper.tex, and `prop:time`: for every word function
printing one table, the stage maps the print inputs `printsWord` to the printed tables `tablesWord`, one call per
table (`tablesStage`, the field `ReconstructPhases.tables`). It is the batch `batchP` of the print program with the
table copier (`batchP_exec`, `tableCopier_exec`); its cost is one printing, the copy of its input and the
`2^{n-k}` entries per table, with a factor `(n+1)^{B₁+13}` (`tablesBatch_le`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.Reconstruct.Batch

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.RepairOrdinary.Streaming (marks marks_length marks_append)
open NearQuarticWires.Control
open NearQuarticWires.Greedy NearQuarticWires.Program
open NearCubicGates.Close.Interfaces (listWord Call)
open NearQuarticWires.Reconstruct

variable {B1 B2 : ℕ}

theorem sum_intWord_le (zs : List ℤ) :
    (zs.map fun z => 60 * (NearCubicGates.Close.Interfaces.intWord z).length + 121 + 4).sum ≤
      60 * (zs.flatMap NearCubicGates.Close.Interfaces.intWord).length + 125 * zs.length := by
  induction zs with
  | nil => simp
  | cons z zs ih => simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append,
      List.length_cons]; omega

/-- **The cost of copying a table** is linear in the table, with the bit length of its count. -/
theorem tableCopyCost_le (zs : List ℤ) (L : ℕ) (hL : natBitLength zs.length ≤ L) :
    tableCopyCost zs ≤ 300 * (L + 10) * (zs.length + 2) +
      70 * (listWord NearCubicGates.Close.Interfaces.intWord zs).length := by
  have hp := two_pow_natBitLength_le zs.length
  have hsum := sum_intWord_le zs
  have hlw : (zs.flatMap NearCubicGates.Close.Interfaces.intWord).length ≤
      (listWord NearCubicGates.Close.Interfaces.intWord zs).length := by
    simp [listWord]
  have h1 : (natBitLength zs.length + 2) * (40 * 2 ^ natBitLength zs.length + 40) ≤ (L + 10) * (80 * zs.length + 120) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h2 : (natBitLength zs.length + 10) * (100 * zs.length + 200) ≤ (L + 10) * (100 * zs.length + 200) :=
    Nat.mul_le_mul (by omega) le_rfl
  unfold tableCopyCost NearCubicGates.Close.Codec.copyListCost
  rw [List.map_map] at *
  simp only [Function.comp_def] at *
  nlinarith


/-! ## The run on a child -/

/-- The register capacity of the stage `tables`. -/
noncomputable def tablesCap (q : ChildRequest B1 B2) (B : ℕ) : ℕ :=
  2 ^ ((printsWord q).length + (tablesWord q).length + B + 10)

theorem le_two_pow_add (y : ℕ) : 10 * (y + 10) ≤ 2 ^ (y + 10) := by
  have h1 : y < 2 ^ y := Nat.lt_two_pow_self
  have h2 : 2 ^ (y + 10) = 1024 * 2 ^ y := by rw [pow_add]; norm_num; ring
  omega

theorem mem_printList_child {q : ChildRequest B1 B2} {r : PrintRequest B1 B2} (hr : r ∈ printList q) :
    r.child = q := by
  obtain ⟨s, σ, δ, p, ρ, -, -, rfl⟩ := mem_printList hr
  rfl

/-- **The stage `tables` on a child.** -/
theorem tablesRun {printBudget : PrintRequest B1 B2 → ℕ} (printBound : Call → List Bool → ℕ)
    (print : WordFunction (PrintRequest B1 B2) printInput
      (fun r => listWord NearCubicGates.Close.Interfaces.intWord (printTable r)) printBudget)
    (hprint : ∀ r : PrintRequest B1 B2, (printIndexWord r).length ≤ (r.child.call.n + 1) ^ sizeExp B1 B2 →
      printBudget r ≤ printBound r.child.call r.child.witness) (q : ChildRequest B1 B2) :
    ∃ τ, WXExec (tablesCap q (printBound q.call q.witness)) (batchP print.program (tableCopier print.program))
      (gammaStart _ (printsWord q)) τ
      (batchCost (contextWord q) printIndexWord printInput
        (fun r => listWord NearCubicGates.Close.Interfaces.intWord (printTable r)) (printBound q.call q.witness)
        (fun r => tableCopyCost (printTable r)) (printList q)) ∧
      τ.st (cOUT _) = frame (tablesWord q) := by
  have hB : ∀ r ∈ printList q, printBudget r ≤ printBound q.call q.witness := by
    intro r hr
    have := hprint r (printIndexWord_le_sizeExp hr)
    rwa [mem_printList_child hr] at this
  have hout : ∀ r ∈ printList q,
      (listWord NearCubicGates.Close.Interfaces.intWord (printTable r)).length ≤ printBound q.call q.witness + 1 :=
    fun r hr => (output_length_le print r).trans (by have := hB r hr; omega)
  have hUl : (tablesWord q).length = (batchOut (contextWord q) printIndexWord
      (fun r => listWord NearCubicGates.Close.Interfaces.intWord (printTable r)) (printList q)).length := rfl
  have hWl : (printsWord q).length = (frame (contextWord q) ++ listWord (fun r => frame (printIndexWord r) ++
      frame (printInput r)) (printList q)).length := rfl
  exact batchP_exec _ print (tableCopier print.program) (tableCopier_avoids _) printIndexWord
    (fun r => tableCopyCost (printTable r)) (printBound q.call q.witness) (contextWord q) (printList q) hB
    (fun r hr σ hO hOh hT hR => tableCopier_exec _ _ (printTable r) σ hO hOh hT hR (by
      have h1 := hout r hr
      have h2 := (listWord_count NearCubicGates.Close.Interfaces.intWord (printTable r)
        (fun z => by have := natBitLength_le_intWord z; omega)).1
      have h3 : 2 ^ (natBitLength (printTable r).length + 1) ≤ 2 ^ (printBound q.call q.witness + 2) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have h4 : 2 ^ (printBound q.call q.witness + 2) * 16 ≤ tablesCap q (printBound q.call q.witness) := by
        unfold tablesCap
        calc 2 ^ (printBound q.call q.witness + 2) * 16 = 2 ^ (printBound q.call q.witness + 6) := by ring
          _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h5 : printBound q.call q.witness + 2 < 2 ^ (printBound q.call q.witness + 2) := Nat.lt_two_pow_self
      omega))
    (by rw [← hWl, ← hUl]; exact le_two_pow_add _)


/-! ## The cost -/

/-- The size of one table item: the bound, the inputs, the columns, the index bound. -/
noncomputable def tableItemSize (q : ChildRequest B1 B2) (B : ℕ) : ℕ :=
  B + (prepWord B1 B2 q.call q.witness).length + (gammaTableWord q).length + q.cellCall.ncol +
    (q.call.n + 1) ^ sizeExp B1 B2

theorem ncol_bits (q : ChildRequest B1 B2) : natBitLength q.cellCall.ncol ≤ q.call.n + 1 := by
  show natBitLength (2 ^ (q.call.n - q.selected.1.k)) ≤ _
  rw [natBitLength_two_pow]; omega

/-- **One table costs a polynomial in its size.** -/
theorem tablesItem_le (q : ChildRequest B1 B2) (B : ℕ) (r : PrintRequest B1 B2) (hr : r ∈ printList q)
    (hout : (listWord NearCubicGates.Close.Interfaces.intWord (printTable r)).length ≤ B + 1) :
    itemCost (printIndexWord r).length (printInput r).length B (tableCopyCost (printTable r)) + 2 ≤
      1000 * (q.call.n + 11) * (tableItemSize q B + 1) := by
  have hc := mem_printList_child hr
  have hidx := printIndexWord_le_sizeExp hr
  rw [hc] at hidx
  have hinp : (printInput r).length = (prepWord B1 B2 q.call q.witness).length + (gammaTableWord q).length +
      (printIndexWord r).length := by
    simp only [printInput, hc, List.length_append]
  have hlen : (printTable r).length = q.cellCall.ncol := by simp [printTable, hc]
  have hcp := tableCopyCost_le (printTable r) (q.call.n + 1) (by rw [hlen]; exact ncol_bits q)
  rw [hlen] at hcp
  have hX1 : 1 ≤ (q.call.n + 1) ^ sizeExp B1 B2 := Nat.one_le_pow _ _ (by omega)
  have hm : 300 * (q.call.n + 1 + 10) * (q.cellCall.ncol + 2) ≤ 300 * (q.call.n + 11) * (tableItemSize q B + 1) :=
    Nat.mul_le_mul_left _ (by unfold tableItemSize; omega)
  have hS : tableItemSize q B + 1 ≤ (q.call.n + 11) * (tableItemSize q B + 1) :=
    Nat.le_mul_of_pos_left _ (by omega)
  unfold itemCost callCost cleanCost
  unfold tableItemSize at hm hS ⊢
  nlinarith


/-- The constant of the batch stages. -/
def batchK (B1 : ℕ) : ℕ := 100000 * (Cells.ParameterArithmetic.preparationCoefficient B1 + 1)

/-- The exponent of the batch stages. -/
def batchE (B1 : ℕ) : ℕ := B1 + 13

theorem itemsCost_le {R : Type} (tag inp : R → List Bool) (B : ℕ) (cpc : R → ℕ) (items : List R) (P : ℕ)
    (h : ∀ r ∈ items, itemCost (tag r).length (inp r).length B (cpc r) + 2 ≤ P) :
    itemsCost tag inp B cpc items ≤ items.length * P + 1 := by
  unfold itemsCost
  have := sum_map_le items (fun r => itemCost (tag r).length (inp r).length B (cpc r) + 2) (fun _ => P) h
  simp only [List.map_const', List.sum_replicate, smul_eq_mul] at this
  omega

theorem batchOut_length {R : Type} (pre : List Bool) (tag out : R → List Bool) (items : List R) (P : ℕ)
    (h : ∀ r ∈ items, (tag r).length + (out r).length ≤ P) :
    (batchOut pre tag out items).length ≤ pre.length + (RepairRepresentation.natWord items.length).length +
      items.length * P := by
  have := sum_map_le items (fun r => (tag r).length + (out r).length) (fun _ => P) h
  simp only [List.map_const', List.sum_replicate, smul_eq_mul] at this
  simp only [batchOut, listWord, List.length_append, List.length_flatMap]
  omega

/-- **The stage `tables` fits its cost.** -/
theorem tablesBatch_le (q : ChildRequest B1 B2) (printBound : Call → List Bool → ℕ)
    (hout : ∀ r ∈ printList q, (listWord NearCubicGates.Close.Interfaces.intWord (printTable r)).length ≤
      printBound q.call q.witness + 1) :
    2 * batchCost (contextWord q) printIndexWord printInput
        (fun r => listWord NearCubicGates.Close.Interfaces.intWord (printTable r)) (printBound q.call q.witness)
        (fun r => tableCopyCost (printTable r)) (printList q) + 2 ≤
      batchK B1 * (q.call.n + 1) ^ batchE B1 * tablesCost q printBound := by
  have hT0 : tablesCost q printBound = tableCount q * tableItemSize q (printBound q.call q.witness) +
      (gammaWord q).length + 1 := rfl
  have hX1 : 1 ≤ (q.call.n + 1) ^ sizeExp B1 B2 := Nat.one_le_pow _ _ (by omega)
  have hS1 : 1 ≤ tableItemSize q (printBound q.call q.witness) := by unfold tableItemSize; omega
  have hm := printList_length_le q
  have hitems := itemsCost_le printIndexWord printInput (printBound q.call q.witness)
    (fun r => tableCopyCost (printTable r)) (printList q) _
    (fun r hr => tablesItem_le q _ r hr (hout r hr))
  have hU := batchOut_length (contextWord q) printIndexWord
    (fun r => listWord NearCubicGates.Close.Interfaces.intWord (printTable r)) (printList q)
    (tableItemSize q (printBound q.call q.witness) + 1) (fun r hr => by
      have := printIndexWord_le_sizeExp hr
      rw [mem_printList_child hr] at this
      have := hout r hr
      unfold tableItemSize; omega)
  have hctx := contextWord_length_le q
  have hE : envelope q ≤ Cells.ParameterArithmetic.preparationCoefficient B1 * (q.call.n + 1) ^ batchE B1 := by
    rw [envelope_eq]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by unfold batchE; omega))
  have hnw := natWord_length_le_self (printList q).length
  set N := (q.call.n + 1) ^ batchE B1 with hN
  set T0 := tablesCost q printBound with hT0'
  set Tc := tableCount q with hTc
  set S := tableItemSize q (printBound q.call q.witness) with hS
  set C := Cells.ParameterArithmetic.preparationCoefficient B1 with hC
  have hN1 : q.call.n + 11 ≤ 11 * N := by
    have : q.call.n + 1 ≤ N := by
      calc q.call.n + 1 = (q.call.n + 1) ^ 1 := (pow_one _).symm
        _ ≤ N := Nat.pow_le_pow_right (by omega) (by unfold batchE; omega)
    omega
  have hN0 : 1 ≤ N := Nat.one_le_pow _ _ (by omega)
  have hTS : Tc ≤ Tc * S := Nat.le_mul_of_pos_right _ (by omega)
  have hTT : Tc * (S + 1) ≤ 2 * T0 := by rw [hT0, mul_add, mul_one]; omega
  have hmS : (printList q).length * (S + 1) ≤ Tc * (S + 1) := Nat.mul_le_mul_right _ hm
  have hP1 : (printList q).length * (1000 * (q.call.n + 11) * (S + 1)) ≤ 1000 * ((11 * N) * (2 * T0)) := by
    calc (printList q).length * (1000 * (q.call.n + 11) * (S + 1))
        = 1000 * ((q.call.n + 11) * ((printList q).length * (S + 1))) := by ring
      _ ≤ 1000 * ((11 * N) * (2 * T0)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul hN1 (hmS.trans hTT))
  have hNT : T0 ≤ N * T0 := Nat.le_mul_of_pos_left _ (by omega)
  have hT01 : 1 ≤ T0 := by rw [hT0]; omega
  have hCN : C * N ≤ C * N * T0 := Nat.le_mul_of_pos_right _ (by omega)
  have hNT1 : 1 ≤ N * T0 := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  unfold batchCost batchK
  rw [← hC]
  have hG : (gammaWord q).length ≤ T0 := by rw [hT0]; omega
  nlinarith [hitems, hU, hctx, hE, hnw, hP1, hNT, hCN, hNT1, hG, hTT, hmS, hm]


/-! ## The stage -/

theorem tables_hout {printBudget : PrintRequest B1 B2 → ℕ} (printBound : Call → List Bool → ℕ)
    (print : WordFunction (PrintRequest B1 B2) printInput
      (fun r => listWord NearCubicGates.Close.Interfaces.intWord (printTable r)) printBudget)
    (hprint : ∀ r : PrintRequest B1 B2, (printIndexWord r).length ≤ (r.child.call.n + 1) ^ sizeExp B1 B2 →
      printBudget r ≤ printBound r.child.call r.child.witness) (q : ChildRequest B1 B2) :
    ∀ r ∈ printList q, (listWord NearCubicGates.Close.Interfaces.intWord (printTable r)).length ≤
      printBound q.call q.witness + 1 := fun r hr => by
  have h1 := output_length_le print r
  have h2 := hprint r (printIndexWord_le_sizeExp hr)
  rw [mem_printList_child hr] at h2
  omega

/-- **The stage `tables`** (`ReconstructPhases.tables`; `lem:print`(a), paper/paper.tex, with
`prop:time`): for every word function printing one table, the batch of its calls maps
`printsWord` to the framed `tablesWord` within `batchK (n+1)^{batchE} tablesCost`. -/
noncomputable def tablesStage (B1 B2 : ℕ) : ∀ (printBudget : PrintRequest B1 B2 → ℕ)
    (printBound : Call → List Bool → ℕ),
    WordFunction (PrintRequest B1 B2) printInput
      (fun r => listWord NearCubicGates.Close.Interfaces.intWord (printTable r)) printBudget →
    (∀ r : PrintRequest B1 B2, (printIndexWord r).length ≤ (r.child.call.n + 1) ^ sizeExp B1 B2 →
      printBudget r ≤ printBound r.child.call r.child.witness) →
    WordFunction (ChildRequest B1 B2) printsWord (fun q => frame (tablesWord q))
      (fun q => batchK B1 * (q.call.n + 1) ^ batchE B1 * tablesCost q printBound) :=
  fun _ printBound print hprint =>
    NearCubicGates.Close.Expand.PolyTab.wordFunction_of_ideal (batchP print.program (tableCopier print.program))
      (cOUT _) (by simp [cOUT]) (fun q => tablesCap q (printBound q.call q.witness)) (fun _ _ => 0)
      (fun q => batchCost (contextWord q) printIndexWord printInput
        (fun r => listWord NearCubicGates.Close.Interfaces.intWord (printTable r)) (printBound q.call q.witness)
        (fun r => tableCopyCost (printTable r)) (printList q))
      (fun q => tablesBatch_le q printBound (tables_hout printBound print hprint q))
      (fun q => ⟨rfl, tablesRun printBound print hprint q⟩)

end NearQuarticWires.Reconstruct.Batch
