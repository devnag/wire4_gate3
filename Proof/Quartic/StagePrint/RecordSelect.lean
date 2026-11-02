import Proof.Quartic.StagePrint.ChildTuples
import Proof.Gates.WordPrograms.CopyN

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.TabMachine
open NearCubicGates.Close.Expand.PolyTab
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

/-- `lem:print`, paper/paper.tex: one actual fixed-width record is selected by its explicit occurrence index. -/
structure RecordSelectRequest where
  L : ℕ
  values : List ℕ
  index : Fin values.length
  width_pos : 1≤L

/-- `lem:print`, paper/paper.tex: the complete eleven-field input for one Cartesian child step. -/
def RecordSelectRequest.word (r : RecordSelectRequest) : List Bool :=
  Top.loadRec (recStream (r.values.map (binary r.L)))
    (List.replicate r.index.val true) [] [] [] [] [] [] [] [] []

/-- `lem:print`, paper/paper.tex: the full cold-input load is included in the cost. -/
def RecordSelectRequest.loadCost (r : RecordSelectRequest) : ℕ :=
  Top.loadCost (recStream (r.values.map (binary r.L)))
    (List.replicate r.index.val true) [] [] [] [] [] [] [] [] []

/-- `lem:print`, paper/paper.tex: bounded storage for the framed input fields. -/
def RecordSelectRequest.loadCapacity (r : RecordSelectRequest) : ℕ :=
  2 * r.word.length + 1 + Top.loadChainCost
    (recStream (r.values.map (binary r.L)))
    (List.replicate r.index.val true) [] [] [] [] [] [] [] [] []

/-- `lem:print`, paper/paper.tex: the exact field bank after extraction. -/
def RecordSelectRequest.fields (r : RecordSelectRequest) : Fin 13 → List Bool :=
  ![frame r.word,r.word,recStream (r.values.map (binary r.L)),
    List.replicate r.index.val true,[],[],[],[],[],[],[],[],[]]

/-- `lem:print`, paper/paper.tex: a fixed field injection for the Cartesian compiler. -/
def recordLoadMap (i : Fin 14) : Fin 16 := ⟨i.val, by have := i.isLt; omega⟩

/-- `lem:print`, paper/paper.tex: distinct extraction fields. -/
theorem recordLoadMap_injective : Function.Injective recordLoadMap := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun x : Fin 16 => x.val) h

/-- `lem:print`, paper/paper.tex: the fixed physical bank after loading. -/
def RecordSelectRequest.loaded (r : RecordSelectRequest) : WState 15 5 :=
  ⟨fun _ => 0, fun i => if h : i.val < 14 then
    (Fin.addCases (m := 13) (n := 1) (motive := fun _ => List Bool) r.fields
      (fun _ : Fin 1 => List.replicate r.loadCapacity false)) ⟨i.val, h⟩
    else [], fun _ => 0, false⟩

/-- `lem:print`, paper/paper.tex: only extraction storage is initially blank-padded. -/
def RecordSelectRequest.lens (r : RecordSelectRequest) (i : Fin 16) : ℕ :=
  if i.val = 13 then r.loadCapacity else 0

/-- `lem:print`, paper/paper.tex: the actual framed loader, before integer dimensions are read. -/
theorem recordLoad_spec (cap : ℕ) (r : RecordSelectRequest) :
    WXExec cap (.mach Top.loadM recordLoadMap)
      (idealStart 15 5 r.word r.lens) r.loaded r.loadCost := by
  have ld := Top.load_run
    (recStream (r.values.map (binary r.L)))
    (List.replicate r.index.val true) [] [] [] [] [] [] [] [] []
    r.loadCapacity
    (by unfold RecordSelectRequest.loadCapacity RecordSelectRequest.word; omega)
    (by unfold RecordSelectRequest.loadCapacity; omega)
  obtain ⟨actual, hr, hh, ht, _⟩ := ld
  let σ := idealStart 15 5 r.word r.lens
  have hin : (fun j : Fin 14 => σ.st (recordLoadMap j)) =
      Fin.addCases (m := 13) (n := 1) (motive := fun _ => List Bool)
        ![frame r.word, [], [], [], [], [], [], [], [], [], [], [], []]
        (fun _ : Fin 1 => List.replicate r.loadCapacity false) := by
    funext j
    fin_cases j <;> simp [σ, idealStart, recordLoadMap, RecordSelectRequest.lens] <;> rfl
  change run Top.loadM r.loadCost
    (Fin.addCases (m := 13) (n := 1) (motive := fun _ => List Bool)
      ![frame r.word, [], [], [], [], [], [], [], [], [], [], [], []]
      (fun _ : Fin 1 => List.replicate r.loadCapacity false)) = some actual at hr
  rw [← hin] at hr
  obtain ⟨τ, e, dock⟩ := WXExec.mach_run cap recordLoadMap_injective σ (fun _ => rfl) hr
  have hτ : τ = r.loaded := by
    apply WState.eq
    · funext i
      by_cases hi : i.val < 14
      · let j : Fin 14 := ⟨i.val, hi⟩
        have hij : recordLoadMap j = i := Fin.ext rfl
        rw [← hij, dock.sh, hh]
        rfl
      · have hn : ∀ j, recordLoadMap j ≠ i := by
          intro j h
          have hv := congrArg Fin.val h
          have := j.isLt
          simp only [recordLoadMap, Fin.val_mk] at hv
          omega
        rw [(dock.other i hn).2]
        rfl
    · funext i
      by_cases hi : i.val < 14
      · let j : Fin 14 := ⟨i.val, hi⟩
        have hij : recordLoadMap j = i := Fin.ext rfl
        rw [← hij, dock.st, ht]
        change (Fin.addCases (m := 13) (n := 1) (motive := fun _ => List Bool) _ _ j) =
          r.loaded.st (recordLoadMap j)
        simp only [RecordSelectRequest.loaded, recordLoadMap, Fin.val_mk, j.isLt, dif_pos]
        rfl
      · have hn : ∀ j, recordLoadMap j ≠ i := by
          intro j h
          have hv := congrArg Fin.val h
          have := j.isLt
          simp only [recordLoadMap, Fin.val_mk] at hv
          omega
        rw [(dock.other i hn).1]
        simp [σ, idealStart, RecordSelectRequest.lens, RecordSelectRequest.loaded, hi,
          show i.val ≠ 0 by omega, show i.val ≠ 13 by omega]
        intro hz
        have hv := congrArg Fin.val hz
        change i.val = 0 at hv
        omega
    · exact dock.val
    · exact dock.cell
  exact e.cast cap hτ le_rfl


/-- `lem:print`, paper/paper.tex: record selection includes its physical index read. -/
def RecordSelectRequest.ready (r : RecordSelectRequest) : WState 15 5 := r.loaded.setv 2 r.index.val

/-- `lem:print`, paper/paper.tex: the finite tape and counter capacity includes all indexed scans. -/
def RecordSelectRequest.capacity (r : RecordSelectRequest) : ℕ :=
  1+r.loadCapacity+(r.index.val+1)+(r.values.length+1)*(2*r.L+1)+2*r.index.val

/-- `lem:print`, paper/paper.tex: the record-selection program starts by loading the serialized stream. -/
noncomputable def recordSelectProgram : WMX 15 5 :=
  .seq (.mach Top.loadM recordLoadMap)
    (.seq (unaryRegister 3 4 2) (getAt 2 15 0 1 2 3))

/-- `prop:time`, paper/paper.tex: record loading, index read, and exact record scan are all charged. -/
def RecordSelectRequest.budget (r : RecordSelectRequest) : ℕ :=
  r.loadCost+1+(16*r.index.val+14+1+
    ((r.index.val+1)*(40*r.L+40)+10*(r.index.val+1)*(2*r.L+1)+10))

/-- `lem:print`, paper/paper.tex: the selected record is physically copied in its exact signed-bit encoding. -/
theorem recordSelectProgram_spec (r : RecordSelectRequest) :
    Runs r.capacity recordSelectProgram (idealStart 15 5 r.word r.lens) r.budget
      (fun τ=>τ.st 15=frame (binary r.L r.values[r.index.val])) := by
  refine Runs.seqE (recordLoad_spec r.capacity r) ?_
  have hi:=unaryRegister_spec r.capacity (3 : Fin 16) (4 : Fin 5) 2 (by decide)
    r.loaded r.index.val rfl rfl rfl rfl (by unfold RecordSelectRequest.capacity;omega)
  refine Runs.seqE hi ?_
  have hg:=getAt_spec r.capacity (A:=2) (Wk:=15) (CA:=0) (CW:=1) (N:=2) (K2:=3)
    (by decide) (by decide) r.L r.width_pos r.values r.index.val r.index.isLt r.ready []
    (by change recStream (r.values.map (binary r.L))=recStream (r.values.map (binary r.L))++[];simp)
    rfl (by simp [RecordSelectRequest.ready,RecordSelectRequest.loaded])
    rfl (by simp [RecordSelectRequest.ready,RecordSelectRequest.loaded])
    (by simp [RecordSelectRequest.ready,RecordSelectRequest.loaded])
    (by simp [RecordSelectRequest.ready]) (by simp [RecordSelectRequest.ready,RecordSelectRequest.loaded])
    (by unfold RecordSelectRequest.capacity;omega)
  exact Runs.of hg rfl

/-- `lem:print`, paper/paper.tex: a cold record source yields one framed record, with no preinitialized cursor. -/
noncomputable def recordSelector :
    WordFunction RecordSelectRequest RecordSelectRequest.word
      (fun r=>frame (binary r.L r.values[r.index.val])) (fun r=>2*r.budget+2) :=
  wordFunction_of_ideal recordSelectProgram (15 : Fin 16) (by decide)
    RecordSelectRequest.capacity RecordSelectRequest.lens RecordSelectRequest.budget
    (fun _=>le_rfl) (fun r=>⟨by rfl,recordSelectProgram_spec r⟩)

end NearQuarticWires.StagePrint
