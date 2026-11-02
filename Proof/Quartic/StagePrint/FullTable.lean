import Proof.Quartic.StagePrint.UnaryRegister
import Proof.Wire_3_5.CompilerMachineTopLoad
import Proof.Gates.Expand.PolyTabPack

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.CompetitorCrossScheduler (producer)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.Expand.PolyTab (idealStart wordFunction_of_ideal)
open NearCubicGates.Close.TabMachine
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicGates.Close.WordPrograms.SInt (encS)

/-- `lem:print`, paper/paper.tex: a separated-cut table with a census below its row dimension. -/
structure TableRequest where
  matrix : MatrixScoreBatch.Request
  cuts_le : matrix.cuts.length ≤ matrix.U

/-- `lem:print`, paper/paper.tex: a signed reconstruction width fixed by the request. -/
def TableRequest.q (r : TableRequest) : ℕ := r.matrix.d + 2 * r.matrix.p + 3

/-- `lem:print`, paper/paper.tex: the full number of output columns in the two-half encoding. -/
def TableRequest.count (r : TableRequest) : ℕ := r.matrix.U * r.matrix.U

/-- `lem:print`, paper/paper.tex: all finite dimension words and actual matrix cuts are included in the input. -/
def TableRequest.word (r : TableRequest) : List Bool :=
  Top.loadRec (MatrixScoreBatch.physicalInput r.matrix) (List.replicate r.q true) [false]
    (List.replicate r.count true) (List.replicate (r.q - 1) true) [] [] [] [] [] []

/-- `lem:print`, paper/paper.tex: the input load pays the size of every dimension word. -/
def TableRequest.loadCost (r : TableRequest) : ℕ :=
  Top.loadCost (MatrixScoreBatch.physicalInput r.matrix) (List.replicate r.q true) [false]
    (List.replicate r.count true) (List.replicate (r.q - 1) true) [] [] [] [] [] []

/-- `lem:print`, paper/paper.tex: the load workspace is bounded by the actual framed fields. -/
def TableRequest.loadCapacity (r : TableRequest) : ℕ :=
  2 * r.word.length + 1 + Top.loadChainCost (MatrixScoreBatch.physicalInput r.matrix)
    (List.replicate r.q true) [false] (List.replicate r.count true)
    (List.replicate (r.q - 1) true) [] [] [] [] [] []

/-- `lem:print`, paper/paper.tex: the complete signed table stream. -/
def TableRequest.output (r : TableRequest) : List Bool :=
  recStream ((pvals false (cutTable r.matrix)).map fun z => binary (r.q + 1) (encS z))

/-- `lem:print`, paper/paper.tex: the fixed stream bank for loading and printing a separated table. -/
noncomputable def tableStreams (a : WilliamsAlgorithm) : ℕ := CompetitorCountBanks.tapes (producer a) + 139

/-- `lem:print`, paper/paper.tex: the fourteen load streams have a fixed injection into the table bank. -/
def loadMap (a : WilliamsAlgorithm) (i : Fin 14) : Fin (tableStreams a + 1) :=
  ⟨i.val, by unfold tableStreams; omega⟩

/-- `lem:print`, paper/paper.tex: the input and two metadata streams overlap exactly the loaded fields. -/
noncomputable def tableMap (a : WilliamsAlgorithm)
    (j : Fin (CompetitorCountBanks.tapes (producer a) + 124)) : Fin (tableStreams a + 1) :=
  if j.val = 0 then ⟨2, by unfold tableStreams; omega⟩
  else if j = freshQ a then ⟨3, by unfold tableStreams; omega⟩
  else if j = freshOdd a then ⟨4, by unfold tableStreams; omega⟩
  else ⟨14 + j.val, by have := j.isLt; unfold tableStreams; omega⟩

/-- `lem:print`, paper/paper.tex: the signed table is written to a separate stream. -/
noncomputable def tableOut (a : WilliamsAlgorithm) : Fin (tableStreams a + 1) :=
  ⟨tableStreams a, by omega⟩

/-- `lem:print`, paper/paper.tex: the table bank has no stream aliases. -/
theorem tableMap_injective (a : WilliamsAlgorithm) : Function.Injective (tableMap a) := by
  intro i j hij
  have hi := i.isLt
  have hj := j.isLt
  have hq : (freshQ a).val ≠ 0 := by simp [freshQ]
  have ho : (freshOdd a).val ≠ 0 := by simp [freshOdd]
  have hqo : freshQ a ≠ freshOdd a := by
    intro h; have hh := congrArg Fin.val h; simp [freshQ, freshOdd] at hh
  unfold tableMap at hij
  split_ifs at hij <;> first | assumption | apply Fin.ext <;> simp_all only [Fin.mk.injEq] <;> omega

/-- `lem:print`, paper/paper.tex: every table-call stream avoids its output. -/
theorem tableMap_ne_out (a : WilliamsAlgorithm) (j) : tableMap a j ≠ tableOut a := by
  intro h
  have hv := congrArg Fin.val h
  have hj := j.isLt
  unfold tableMap tableOut at hv
  split_ifs at hv <;> simp only [Fin.val_mk] at hv <;> unfold tableStreams at hv <;> omega

/-- `lem:print`, paper/paper.tex: the fourteen load streams are distinct. -/
theorem loadMap_injective (a : WilliamsAlgorithm) : Function.Injective (loadMap a) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun z : Fin (tableStreams a + 1) => z.val) h


/-- `lem:print`, paper/paper.tex: all input fields after their physical framed load. -/
def TableRequest.fields (r : TableRequest) : Fin 13 → List Bool :=
  ![frame r.word, r.word, MatrixScoreBatch.physicalInput r.matrix, List.replicate r.q true,
    [false], List.replicate r.count true, List.replicate (r.q - 1) true, [], [], [], [], [], []]

/-- `lem:print`, paper/paper.tex: the exact finite bank after field extraction. -/
def TableRequest.loaded (a : WilliamsAlgorithm) (r : TableRequest) : WState (tableStreams a) 10 :=
  ⟨fun _ => 0,
    fun i => if h : i.val < 14 then
      (Fin.addCases (m := 13) (n := 1) (motive := fun _ => List Bool) r.fields (fun _ : Fin 1 => List.replicate r.loadCapacity false)) ⟨i.val, h⟩
      else [], fun _ => 0, false⟩

/-- `lem:print`, paper/paper.tex: the load uses one bounded blank log stream. -/
def tableLens (a : WilliamsAlgorithm) (r : TableRequest) (i : Fin (tableStreams a + 1)) : ℕ :=
  if i.val = 13 then r.loadCapacity else 0

/-- `lem:print`, paper/paper.tex: extraction of the actual framed fields into the table bank. -/
theorem tableLoad_spec (cap : ℕ) (a : WilliamsAlgorithm) (r : TableRequest) :
    WXExec cap (.mach Top.loadM (loadMap a))
      (idealStart (tableStreams a) 10 r.word (tableLens a r)) (r.loaded a) r.loadCost := by
  have ld := Top.load_run (MatrixScoreBatch.physicalInput r.matrix) (List.replicate r.q true) [false]
    (List.replicate r.count true) (List.replicate (r.q - 1) true) [] [] [] [] [] [] r.loadCapacity
    (by unfold TableRequest.loadCapacity TableRequest.word; omega)
    (by unfold TableRequest.loadCapacity; omega)
  obtain ⟨actual, hr, hh, ht, _⟩ := ld
  let σ := idealStart (tableStreams a) 10 r.word (tableLens a r)
  have hin : (fun j : Fin 14 => σ.st (loadMap a j)) =
      Fin.addCases (m := 13) (n := 1) (motive := fun _ => List Bool) ![frame r.word, [], [], [], [], [], [], [], [], [], [], [], []]
        (fun _ : Fin 1 => List.replicate r.loadCapacity false) := by
    funext j
    fin_cases j <;> simp [σ, idealStart, loadMap, tableLens] <;> rfl
  change run Top.loadM r.loadCost
    (Fin.addCases (m := 13) (n := 1) (motive := fun _ => List Bool)
      ![frame r.word, [], [], [], [], [], [], [], [], [], [], [], []]
      (fun _ : Fin 1 => List.replicate r.loadCapacity false)) = some actual at hr
  rw [← hin] at hr
  obtain ⟨τ, e, dock⟩ := WXExec.mach_run cap (loadMap_injective a) σ (fun _ => rfl) hr
  have hτ : τ = r.loaded a := by
    apply WState.eq
    · funext i
      by_cases hi : i.val < 14
      · let j : Fin 14 := ⟨i.val, hi⟩
        have hij : loadMap a j = i := Fin.ext rfl
        rw [← hij, dock.sh, hh]
        rfl
      · have hn : ∀ j, loadMap a j ≠ i := by
          intro j h
          have hv := congrArg Fin.val h
          have := j.isLt
          simp only [loadMap, Fin.val_mk] at hv
          omega
        rw [(dock.other i hn).2]
        rfl
    · funext i
      by_cases hi : i.val < 14
      · let j : Fin 14 := ⟨i.val, hi⟩
        have hij : loadMap a j = i := Fin.ext rfl
        rw [← hij, dock.st, ht]
        change (Fin.addCases (m := 13) (n := 1) (motive := fun _ => List Bool) _ _ j) = (r.loaded a).st (loadMap a j)
        simp only [TableRequest.loaded, loadMap, Fin.val_mk, j.isLt, dif_pos]
        rfl
      · have hn : ∀ j, loadMap a j ≠ i := by
          intro j h
          have hv := congrArg Fin.val h
          have := j.isLt
          simp only [loadMap, Fin.val_mk] at hv
          omega
        rw [(dock.other i hn).1]
        simp [σ, idealStart, tableLens, TableRequest.loaded, hi, show i.val ≠ 0 by omega,
          show i.val ≠ 13 by omega]
        intro hz
        have hv := congrArg Fin.val hz
        change i.val = 0 at hv
        omega
    · exact dock.val
    · exact dock.cell
  exact e.cast cap hτ le_rfl

/-- `lem:print`, paper/paper.tex: the three distinguished table streams are loaded with their actual words. -/
theorem loaded_table_input (a : WilliamsAlgorithm) (r : TableRequest) :
    ∀ j, (r.loaded a).st (tableMap a j) =
      CompetitorCountTable.input (producer a) r.matrix r.q false j := by
  intro j
  rw [printerIn_val]
  by_cases hj : j.val = 0
  · simp [tableMap, hj, TableRequest.loaded, TableRequest.fields] <;> rfl
  · by_cases hQ : j = freshQ a
    · simp [tableMap, hj, hQ, TableRequest.loaded, TableRequest.fields, freshQ] <;> rfl
    · by_cases hO : j = freshOdd a
      · simp [tableMap, hj, hQ, hO, TableRequest.loaded, TableRequest.fields, freshQ, freshOdd] <;> rfl
      · simp [tableMap, hj, hQ, hO, TableRequest.loaded]

/-- `lem:print`, paper/paper.tex: loading and dimension reads precede the signed table pass. -/
noncomputable def fullTableProgram (a : WilliamsAlgorithm) : WMX (tableStreams a) 10 :=
  .seq (.mach Top.loadM (loadMap a)) <|
    .seq (unaryRegister ⟨5, by unfold tableStreams; omega⟩ 4 0) <|
    .seq (unaryRegister ⟨3, by unfold tableStreams; omega⟩ 4 2) <|
    .seq (unaryRegister ⟨6, by unfold tableStreams; omega⟩ 4 3) <|
      signedTable a (tableMap a) (tableOut a) 0 1 2 3 4 5 6 7 8

/-- `lem:print`, paper/paper.tex: complete finite loading, dimensions and table cost. -/
noncomputable def fullTableCost (a : WilliamsAlgorithm) (r : TableRequest) : ℕ :=
  r.loadCost + 1 + (16 * r.count + 14 + 1 +
    (16 * r.q + 14 + 1 + (16 * (r.q - 1) + 14 + 1 + signedTableCost a r.matrix r.q)))

/-- `lem:print`, paper/paper.tex: a common register capacity includes the complete table stream. -/
def fullTableCapacity (r : TableRequest) : ℕ :=
  r.loadCapacity + r.count * (2 * r.q + 3) + 2 * r.q + 4 + r.count + r.q + 1


/-- `lem:print`, paper/paper.tex: signed cut values stay inside the declared reconstruction frame. -/
theorem TableRequest.value_bound (r : TableRequest) (i j : Fin r.matrix.U) :
    (cutTable r.matrix i j).natAbs < 2 ^ (r.q - 1) := by
  let f : Fin r.matrix.Gates → ℤ := fun g => MatrixScoreBatch.weight r.matrix g *
    ((decide (MatrixScoreBatch.leftScore r.matrix i g ≤ MatrixScoreBatch.rightScore r.matrix g j)).toNat : ℤ)
  have hterm : ∀ g, (f g).natAbs ≤ 2 ^ r.matrix.p := by
    intro g
    have hg := (r.matrix.fits (r.matrix.cuts.get g) (List.get_mem _ g)).2.2
    unfold f MatrixScoreBatch.weight
    rw [Int.natAbs_mul]
    cases decide (MatrixScoreBatch.leftScore r.matrix i g ≤ MatrixScoreBatch.rightScore r.matrix g j) <;>
      simp_all <;> omega
  have hs : (cutTable r.matrix i j).natAbs ≤ r.matrix.cuts.length * 2 ^ r.matrix.p := by
    apply (Int.natAbs_sum_le Finset.univ f).trans
    calc
      ∑ g, (f g).natAbs ≤ ∑ _g : Fin r.matrix.Gates, 2 ^ r.matrix.p :=
        Finset.sum_le_sum (fun g _ => hterm g)
      _ = _ := by simp [MatrixScoreBatch.Request.Gates, Fintype.card_fin]; exact Fintype.card_fin _
  have h1 := Nat.mul_le_mul_right (2 ^ r.matrix.p) r.cuts_le
  have h2 : r.matrix.U * 2 ^ r.matrix.p < 2 ^ (r.q - 1) := by
    unfold MatrixScoreBatch.Request.U TableRequest.q
    rw [← pow_add]
    exact Nat.pow_lt_pow_right (by decide) (by omega)
  exact hs.trans_lt (h1.trans_lt h2)

/-- `lem:print`, paper/paper.tex: the whole finite program prints the exact signed affine-pullback table. -/
theorem fullTableProgram_spec (a : WilliamsAlgorithm) (r : TableRequest) :
    Runs (fullTableCapacity r) (fullTableProgram a)
      (idealStart (tableStreams a) 10 r.word (tableLens a r)) (fullTableCost a r)
      (fun τ => τ.st (tableOut a) = r.output) := by
  let cap := (fullTableCapacity r)
  let σ := r.loaded a
  have hN : r.count + 1 ≤ cap := by dsimp [cap, fullTableCapacity]; omega
  have hQ : r.q + 1 ≤ cap := by dsimp [cap, fullTableCapacity]; omega
  have hQm : r.q - 1 + 1 ≤ cap := by omega
  have e0 := tableLoad_spec cap a r
  have e1 := unaryRegister_spec cap (⟨5, by unfold tableStreams; omega⟩ : Fin (tableStreams a + 1))
    (4 : Fin 10) 0 (by decide) σ r.count
    (by simp [σ, TableRequest.loaded, TableRequest.fields]; rfl) rfl rfl rfl hN
  let σ1 := σ.setv 0 r.count
  have e2 := unaryRegister_spec cap (⟨3, by unfold tableStreams; omega⟩ : Fin (tableStreams a + 1))
    (4 : Fin 10) 2 (by decide) σ1 r.q
    (by simp [σ1, σ, TableRequest.loaded, TableRequest.fields]; rfl) rfl rfl rfl hQ
  let σ2 := σ1.setv 2 r.q
  have e3 := unaryRegister_spec cap (⟨6, by unfold tableStreams; omega⟩ : Fin (tableStreams a + 1))
    (4 : Fin 10) 3 (by decide) σ2 (r.q - 1)
    (by simp [σ2, σ1, σ, TableRequest.loaded, TableRequest.fields]; rfl) rfl rfl rfl hQm
  let σ3 := σ2.setv 3 (r.q - 1)
  have e4 := signedTable_spec cap a (qmap := tableMap a) (OUT := tableOut a)
    (NR := 0) (N2 := 1) (QR := 2) (Q1R := 3) (K2 := 4) (CO := 5) (CP := 6) (TOP := 7) (SEEN := 8)
    (tableMap_injective a) (tableMap_ne_out a) (by decide) r.matrix r.q σ3
    (loaded_table_input a r) (fun _ => rfl)
    (by simp [σ3, σ2, σ1, σ, TableRequest.loaded, tableOut, tableStreams]) rfl
    rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (by unfold TableRequest.q; omega)
    (by rw [CompetitorSameBucketColdDense.width_eq]; rfl)
    r.value_bound (by dsimp [cap, fullTableCapacity, TableRequest.count]; omega)
  obtain ⟨τ, e4, hout, _, _, _⟩ := e4
  exact ⟨τ, WXExec.seq e0 (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 e4))), hout⟩

/-- `lem:print`, paper/paper.tex: an actual word function prints the complete signed separated-equation table. -/
noncomputable def fullTablePrinter (a : WilliamsAlgorithm) :
    WordFunction TableRequest TableRequest.word TableRequest.output (fun r => 2 * fullTableCost a r + 2) :=
  wordFunction_of_ideal (fullTableProgram a) (tableOut a) (by unfold tableOut tableStreams; simp)
    fullTableCapacity (tableLens a) (fullTableCost a) (fun _ => le_rfl) (by
      intro r
      refine ⟨?_, ?_⟩
      · simp [tableLens, tableOut, tableStreams]
      · exact fullTableProgram_spec a r)

end NearQuarticWires.StagePrint
