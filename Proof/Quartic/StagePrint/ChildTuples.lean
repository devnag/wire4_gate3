import Proof.Quartic.StagePrint.FullTable
import Proof.Gates.TabMachine.Tuple

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.TabMachine
open NearCubicGates.Close.Expand.PolyTab
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

/-- `lem:print`, paper/paper.tex: original exact children and accumulated monomial tuples with their common signed field width. -/
structure ChildTupleRequest where
  L : ℕ
  N : ℕ
  M : ℕ
  children : List (List ℤ)
  tuples : List (List ℤ)
  width_pos : 1 ≤ L
  children_length : ∀ x ∈ children, x.length = N
  tuples_length : ∀ x ∈ tuples, x.length = M

/-- `lem:print`, paper/paper.tex: the complete eleven-field input for one Cartesian child step. -/
def ChildTupleRequest.word (r : ChildTupleRequest) : List Bool :=
  Top.loadRec (recStream ((fieldNums r.children).map (binary r.L)))
    (recStream ((fieldNums r.tuples).map (binary r.L)))
    (List.replicate r.N true) (List.replicate r.M true)
    (List.replicate r.children.length true) (List.replicate r.tuples.length true) [] [] [] [] []

/-- `lem:print`, paper/paper.tex: the full cold-input load is included in the cost. -/
def ChildTupleRequest.loadCost (r : ChildTupleRequest) : ℕ :=
  Top.loadCost (recStream ((fieldNums r.children).map (binary r.L)))
    (recStream ((fieldNums r.tuples).map (binary r.L)))
    (List.replicate r.N true) (List.replicate r.M true)
    (List.replicate r.children.length true) (List.replicate r.tuples.length true) [] [] [] [] []

/-- `lem:print`, paper/paper.tex: bounded storage for the framed input fields. -/
def ChildTupleRequest.loadCapacity (r : ChildTupleRequest) : ℕ :=
  2 * r.word.length + 1 + Top.loadChainCost
    (recStream ((fieldNums r.children).map (binary r.L)))
    (recStream ((fieldNums r.tuples).map (binary r.L)))
    (List.replicate r.N true) (List.replicate r.M true)
    (List.replicate r.children.length true) (List.replicate r.tuples.length true) [] [] [] [] []

/-- `lem:print`, paper/paper.tex: the exact field bank after extraction. -/
def ChildTupleRequest.fields (r : ChildTupleRequest) : Fin 13 → List Bool :=
  ![frame r.word, r.word, recStream ((fieldNums r.children).map (binary r.L)),
    recStream ((fieldNums r.tuples).map (binary r.L)), List.replicate r.N true,
    List.replicate r.M true, List.replicate r.children.length true,
    List.replicate r.tuples.length true, [], [], [], [], []]

/-- `lem:print`, paper/paper.tex: a fixed field injection for the Cartesian compiler. -/
def tupleLoadMap (i : Fin 14) : Fin 20 := ⟨i.val, by have := i.isLt; omega⟩

/-- `lem:print`, paper/paper.tex: distinct extraction fields. -/
theorem tupleLoadMap_injective : Function.Injective tupleLoadMap := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun x : Fin 20 => x.val) h

/-- `lem:print`, paper/paper.tex: the fixed physical bank after loading. -/
def ChildTupleRequest.loaded (r : ChildTupleRequest) : WState 19 18 :=
  ⟨fun _ => 0, fun i => if h : i.val < 14 then
    (Fin.addCases (m := 13) (n := 1) (motive := fun _ => List Bool) r.fields
      (fun _ : Fin 1 => List.replicate r.loadCapacity false)) ⟨i.val, h⟩
    else [], fun _ => 0, false⟩

/-- `lem:print`, paper/paper.tex: only extraction storage is initially blank-padded. -/
def ChildTupleRequest.lens (r : ChildTupleRequest) (i : Fin 20) : ℕ :=
  if i.val = 13 then r.loadCapacity else 0

/-- `lem:print`, paper/paper.tex: the actual framed loader, before integer dimensions are read. -/
theorem tupleLoad_spec (cap : ℕ) (r : ChildTupleRequest) :
    WXExec cap (.mach Top.loadM tupleLoadMap)
      (idealStart 19 18 r.word r.lens) r.loaded r.loadCost := by
  have ld := Top.load_run
    (recStream ((fieldNums r.children).map (binary r.L)))
    (recStream ((fieldNums r.tuples).map (binary r.L)))
    (List.replicate r.N true) (List.replicate r.M true)
    (List.replicate r.children.length true) (List.replicate r.tuples.length true) [] [] [] [] []
    r.loadCapacity
    (by unfold ChildTupleRequest.loadCapacity ChildTupleRequest.word; omega)
    (by unfold ChildTupleRequest.loadCapacity; omega)
  obtain ⟨actual, hr, hh, ht, _⟩ := ld
  let σ := idealStart 19 18 r.word r.lens
  have hin : (fun j : Fin 14 => σ.st (tupleLoadMap j)) =
      Fin.addCases (m := 13) (n := 1) (motive := fun _ => List Bool)
        ![frame r.word, [], [], [], [], [], [], [], [], [], [], [], []]
        (fun _ : Fin 1 => List.replicate r.loadCapacity false) := by
    funext j
    fin_cases j <;> simp [σ, idealStart, tupleLoadMap, ChildTupleRequest.lens] <;> rfl
  change run Top.loadM r.loadCost
    (Fin.addCases (m := 13) (n := 1) (motive := fun _ => List Bool)
      ![frame r.word, [], [], [], [], [], [], [], [], [], [], [], []]
      (fun _ : Fin 1 => List.replicate r.loadCapacity false)) = some actual at hr
  rw [← hin] at hr
  obtain ⟨τ, e, dock⟩ := WXExec.mach_run cap tupleLoadMap_injective σ (fun _ => rfl) hr
  have hτ : τ = r.loaded := by
    apply WState.eq
    · funext i
      by_cases hi : i.val < 14
      · let j : Fin 14 := ⟨i.val, hi⟩
        have hij : tupleLoadMap j = i := Fin.ext rfl
        rw [← hij, dock.sh, hh]
        rfl
      · have hn : ∀ j, tupleLoadMap j ≠ i := by
          intro j h
          have hv := congrArg Fin.val h
          have := j.isLt
          simp only [tupleLoadMap, Fin.val_mk] at hv
          omega
        rw [(dock.other i hn).2]
        rfl
    · funext i
      by_cases hi : i.val < 14
      · let j : Fin 14 := ⟨i.val, hi⟩
        have hij : tupleLoadMap j = i := Fin.ext rfl
        rw [← hij, dock.st, ht]
        change (Fin.addCases (m := 13) (n := 1) (motive := fun _ => List Bool) _ _ j) =
          r.loaded.st (tupleLoadMap j)
        simp only [ChildTupleRequest.loaded, tupleLoadMap, Fin.val_mk, j.isLt, dif_pos]
        rfl
      · have hn : ∀ j, tupleLoadMap j ≠ i := by
          intro j h
          have hv := congrArg Fin.val h
          have := j.isLt
          simp only [tupleLoadMap, Fin.val_mk] at hv
          omega
        rw [(dock.other i hn).1]
        simp [σ, idealStart, ChildTupleRequest.lens, ChildTupleRequest.loaded, hi,
          show i.val ≠ 0 by omega, show i.val ≠ 13 by omega]
        intro hz
        have hv := congrArg Fin.val hz
        change i.val = 0 at hv
        omega
    · exact dock.val
    · exact dock.cell
  exact e.cast cap hτ le_rfl

/-- `lem:print`, paper/paper.tex: four dimension reads precede the exact Cartesian step. -/
def tupleDimensions : WMX 19 18 :=
  .seq (unaryRegister 4 17 6) <|
    .seq (unaryRegister 5 17 9) <|
      .seq (unaryRegister 6 17 11) (unaryRegister 7 17 13)

/-- `lem:print`, paper/paper.tex: the exact register state used by the child-tuple kernel. -/
def ChildTupleRequest.ready (r : ChildTupleRequest) : WState 19 18 :=
  (((r.loaded.setv 6 r.N).setv 9 r.M).setv 11 r.children.length).setv 13 r.tuples.length

/-- `lem:print`, paper/paper.tex: all dimension reads are charged. -/
def ChildTupleRequest.dimensionCost (r : ChildTupleRequest) : ℕ :=
  16 * r.N + 14 + 1 + (16 * r.M + 14 + 1 +
    (16 * r.children.length + 14 + 1 + (16 * r.tuples.length + 14)))

/-- `lem:print`, paper/paper.tex: extraction reads preserve the complete child and tuple streams. -/
theorem tupleDimensions_spec (cap : ℕ) (r : ChildTupleRequest)
    (hN : r.N + 1 ≤ cap) (hM : r.M + 1 ≤ cap)
    (hK : r.children.length + 1 ≤ cap) (hT : r.tuples.length + 1 ≤ cap) :
    WXExec cap tupleDimensions r.loaded r.ready r.dimensionCost := by
  have a1 := unaryRegister_spec cap (4 : Fin 20) (17 : Fin 18) 6 (by decide) r.loaded r.N
    rfl rfl rfl rfl hN
  have a2 := unaryRegister_spec cap (5 : Fin 20) (17 : Fin 18) 9 (by decide)
    (r.loaded.setv 6 r.N) r.M
    rfl rfl
    (by simp [ChildTupleRequest.loaded]) (by simp [ChildTupleRequest.loaded]) hM
  have a3 := unaryRegister_spec cap (6 : Fin 20) (17 : Fin 18) 11 (by decide)
    ((r.loaded.setv 6 r.N).setv 9 r.M) r.children.length
    rfl rfl
    (by simp [ChildTupleRequest.loaded]) (by simp [ChildTupleRequest.loaded]) hK
  have a4 := unaryRegister_spec cap (7 : Fin 20) (17 : Fin 18) 13 (by decide)
    (((r.loaded.setv 6 r.N).setv 9 r.M).setv 11 r.children.length) r.tuples.length
    rfl rfl
    (by simp [ChildTupleRequest.loaded]) (by simp [ChildTupleRequest.loaded]) hT
  exact (a1.seq (a2.seq (a3.seq a4))).cast cap rfl (by rfl)

/-- `lem:print`, paper/paper.tex: fixed child, tuple, output and scratch streams. -/
def childTupleMap : Fin 4 ↪ Fin 20 :=
  ⟨![2, 3, 19, 18], by decide⟩

/-- `lem:print`, paper/paper.tex: the seventeen arithmetic registers remain distinct. -/
def childTupleRegs : Fin 17 ↪ Fin 18 :=
  ⟨fun i => ⟨i.val, by have := i.isLt; omega⟩, by
    intro i j h
    apply Fin.ext
    exact congrArg (fun x : Fin 18 => x.val) h⟩

/-- `lem:print`, paper/paper.tex: the finite capacity covers every read, repeated copy, and Cartesian output. -/
def ChildTupleRequest.capacity (r : ChildTupleRequest) : ℕ :=
  r.loadCapacity + r.N + r.M + r.children.length + r.tuples.length + 10 +
  ((r.children.length * r.N + 1) * (2*r.L+1) + 2*(r.children.length*r.N)) +
  ((r.tuples.length * r.M + 1) * (2*r.L+1) + 2*(r.tuples.length*r.M)) +
  (r.children.length * r.tuples.length * ((r.N+r.M)*(2*r.L+1)) + 1) +
  (2*r.children.length + 2*r.tuples.length + r.children.length*r.N + r.N)

/-- `lem:print`, paper/paper.tex: the loaded state meets the exact precompiled-child invariants. -/
theorem tupleReady_pre (r : ChildTupleRequest) :
    TPre childTupleMap childTupleRegs r.L r.N r.M r.children r.tuples r.ready := by
  constructor
  · exact ⟨[], by simp only [List.append_nil]; rfl⟩
  · rfl
  · exact ⟨[], by simp only [List.append_nil]; rfl⟩
  · rfl
  · rfl
  · simp [ChildTupleRequest.ready, ChildTupleRequest.loaded, childTupleMap]
  · simp [ChildTupleRequest.ready, ChildTupleRequest.loaded, childTupleRegs]
  · simp [ChildTupleRequest.ready, ChildTupleRequest.loaded, childTupleRegs]
  · simp [ChildTupleRequest.ready, ChildTupleRequest.loaded, childTupleRegs]
  · simp [ChildTupleRequest.ready, ChildTupleRequest.loaded, childTupleRegs]
  · simp [ChildTupleRequest.ready, ChildTupleRequest.loaded, childTupleRegs]
  · simp [ChildTupleRequest.ready, ChildTupleRequest.loaded, childTupleRegs]
  · simp [ChildTupleRequest.ready, ChildTupleRequest.loaded, childTupleRegs]
  · simp [ChildTupleRequest.ready, ChildTupleRequest.loaded, childTupleRegs]
  · simp [ChildTupleRequest.ready, ChildTupleRequest.loaded, childTupleRegs]

/-- `lem:print`, paper/paper.tex: cold extraction and exact tuple construction form one fixed program. -/
noncomputable def childTupleProgram : WMX 19 18 :=
  .seq (.mach Top.loadM tupleLoadMap)
    (.seq tupleDimensions (tupleStep childTupleMap childTupleRegs))

/-- `lem:print`, paper/paper.tex: the complete child-step time. -/
def ChildTupleRequest.budget (r : ChildTupleRequest) : ℕ :=
  r.loadCost + 1 + (r.dimensionCost + 1 + tupleCost r.L r.N r.M r.children.length r.tuples.length)

/-- `lem:print`, paper/paper.tex: the output contains every child/tuple pair, preserving all fields and signs. -/
def ChildTupleRequest.output (r : ChildTupleRequest) : List Bool :=
  fieldsRecs r.L (newT r.children r.tuples)

/-- `lem:print`, paper/paper.tex: an actual cold-input Cartesian child machine. -/
theorem childTupleProgram_spec (r : ChildTupleRequest) :
    Runs r.capacity childTupleProgram (idealStart 19 18 r.word r.lens) r.budget
      (fun τ => τ.st 19 = r.output) := by
  refine Runs.seqE (tupleLoad_spec r.capacity r) ?_
  refine Runs.seqE (tupleDimensions_spec r.capacity r ?_ ?_ ?_ ?_) ?_
  all_goals try (unfold ChildTupleRequest.capacity; omega)
  have ht := tupleStep_spec childTupleMap childTupleRegs r.capacity r.L r.N r.M r.width_pos
    r.children r.tuples r.ready [] [] r.children_length r.tuples_length (tupleReady_pre r)
    (by simp [ChildTupleRequest.ready, ChildTupleRequest.loaded, childTupleRegs])
    (by simp [ChildTupleRequest.ready, ChildTupleRequest.loaded, childTupleRegs])
    (by simp [ChildTupleRequest.ready, ChildTupleRequest.loaded, childTupleRegs])
    (by simp [ChildTupleRequest.ready, ChildTupleRequest.loaded, childTupleRegs])
    (by simp [ChildTupleRequest.ready, ChildTupleRequest.loaded, childTupleRegs])
    (by simp [ChildTupleRequest.ready, ChildTupleRequest.loaded, childTupleRegs])
    (by simp [ChildTupleRequest.ready, ChildTupleRequest.loaded, childTupleRegs])
    (by simp [OutOn, ChildTupleRequest.ready, ChildTupleRequest.loaded, childTupleRegs,
      childTupleMap, StablePartition.Workspace.overlay])
    (by unfold TCap ChildTupleRequest.capacity; simp only [List.length_nil, zero_add]; constructor; omega; constructor; omega; constructor <;> omega)
  exact ht.post fun τ h => by
    rcases h.2.1 with ⟨ho, _, _⟩
    simpa [childTupleMap, ChildTupleRequest.output, StablePartition.Workspace.overlay] using ho

/-- `lem:print`, paper/paper.tex: the exact precompiled-child Cartesian product is a physical word function. -/
noncomputable def childTuplePrinter :
    WordFunction ChildTupleRequest ChildTupleRequest.word ChildTupleRequest.output
      (fun r => 2*r.budget+2) :=
  wordFunction_of_ideal childTupleProgram (19 : Fin 20) (by decide)
    ChildTupleRequest.capacity ChildTupleRequest.lens ChildTupleRequest.budget
    (fun _ => le_rfl) (fun r => ⟨by rfl, childTupleProgram_spec r⟩)

end NearQuarticWires.StagePrint
