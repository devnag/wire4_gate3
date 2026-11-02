import Proof.Quartic.StagePrint.OriginalChildMachine
import Proof.Quartic.StagePrint.UnaryRegister
import Proof.Gates.TabMachine.Mono2

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.TabMachine
open NearCubicGates.Close.Expand.PolyTab
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicGates.Close.WordPrograms.SInt (encS)

/-- `lem:print`, paper/paper.tex: a tuple stream and its signed stacking coefficient. -/
structure StackRequest where
  W : ℕ
  s : ℕ
  m : ℕ
  tuples : List (List (List ℤ))
  coefficient : ℤ
  width_pos : 1 ≤ W
  tuple_length : ∀ ls ∈ tuples, ls.length = m
  row_length : ∀ ls ∈ tuples, ∀ l ∈ ls, l.length = s+1
  fields_fit : ∀ x ∈ fieldNums (tuples.map List.flatten), x < 2^(W+1)
  coefficient_fit : encS coefficient < 2^(W+1)
  stack_fit : ∀ ls ∈ tuples, (magL ls+1)^(m+1) < 2^W

/-- `lem:print`, paper/paper.tex: flattened signed input fields in tuple order. -/
def StackRequest.nums (r : StackRequest) : List ℕ := fieldNums (r.tuples.map List.flatten)

/-- `lem:print`, paper/paper.tex: the serialized tuple, constants, and dimension fields. -/
def StackRequest.word (r : StackRequest) : List Bool :=
  Top.loadRec (recStream (r.nums.map (binary (r.W+1))))
    (frame (binary (r.W+1) 0)) (frame (binary (r.W+1) 0))
    (frame (binary (r.W+1) 0)) (frame (binary (r.W+1) (encS r.coefficient)))
    (frame (binary (r.W+1) 2)) (List.replicate (r.m*(r.s+1)) true)
    (List.replicate (r.s+1) true) (List.replicate r.m true)
    (List.replicate r.tuples.length true) []

/-- `lem:print`, paper/paper.tex: full field extraction cost. -/
def StackRequest.loadCost (r : StackRequest) : ℕ :=
  Top.loadCost (recStream (r.nums.map (binary (r.W+1))))
    (frame (binary (r.W+1) 0)) (frame (binary (r.W+1) 0))
    (frame (binary (r.W+1) 0)) (frame (binary (r.W+1) (encS r.coefficient)))
    (frame (binary (r.W+1) 2)) (List.replicate (r.m*(r.s+1)) true)
    (List.replicate (r.s+1) true) (List.replicate r.m true)
    (List.replicate r.tuples.length true) []

/-- `lem:print`, paper/paper.tex: finite storage for every extraction field. -/
def StackRequest.loadCapacity (r : StackRequest) : ℕ :=
  2*r.word.length+1+Top.loadChainCost (recStream (r.nums.map (binary (r.W+1))))
    (frame (binary (r.W+1) 0)) (frame (binary (r.W+1) 0))
    (frame (binary (r.W+1) 0)) (frame (binary (r.W+1) (encS r.coefficient)))
    (frame (binary (r.W+1) 2)) (List.replicate (r.m*(r.s+1)) true)
    (List.replicate (r.s+1) true) (List.replicate r.m true)
    (List.replicate r.tuples.length true) []

/-- `lem:print`, paper/paper.tex: all thirteen loaded fields. -/
def StackRequest.fields (r : StackRequest) : Fin 13 → List Bool :=
  ![frame r.word,r.word,recStream (r.nums.map (binary (r.W+1))),
    frame (binary (r.W+1) 0),frame (binary (r.W+1) 0),frame (binary (r.W+1) 0),
    frame (binary (r.W+1) (encS r.coefficient)),frame (binary (r.W+1) 2),
    List.replicate (r.m*(r.s+1)) true,List.replicate (r.s+1) true,
    List.replicate r.m true,List.replicate r.tuples.length true,[]]

/-- `lem:print`, paper/paper.tex: three disjoint extraction blocks share only the input. -/
def stackLoadMap := originalLoadMap

/-- `lem:print`, paper/paper.tex: distinct fields in every extraction block. -/
theorem stackLoadMap_injective (s : Fin 3) : Function.Injective (stackLoadMap s) :=
  originalLoadMap_injective s

/-- `lem:print`, paper/paper.tex: the three extraction scratch tapes are bounded blank storage. -/
def StackRequest.lens (r : StackRequest) (i : Fin 45) : ℕ :=
  if 40 ≤ i.val ∧ i.val < 43 then r.loadCapacity else 0

/-- `lem:print`, paper/paper.tex: after s blocks, every original coefficient is unchanged. -/
def StackRequest.loaded (r : StackRequest) (s : ℕ) : WState 44 26 :=
  ⟨fun _=>0,fun i=>if i.val=0 then frame r.word else
    if h : 1 ≤ i.val ∧ i.val < 39 ∧ (i.val-1)/13 < s ∧ (i.val-1)%13 < 12 then
      r.fields ⟨(i.val-1)%13+1,by omega⟩
    else List.replicate (r.lens i) false,fun _=>0,false⟩

/-- `lem:print`, paper/paper.tex: the zero-block bank is the physical cold start. -/
theorem stackLoad_zero (r : StackRequest) :
    r.loaded 0 = idealStart 44 26 r.word r.lens := by
  apply WState.eq
  · rfl
  · funext i
    simp [StackRequest.loaded,idealStart]
  · rfl
  · rfl

/-- `lem:print`, paper/paper.tex: each constant field block is physically extracted, with no coefficient constructor assumption. -/
theorem stackLoad_spec (cap : ℕ) (r : StackRequest) (s : Fin 3) :
    WXExec cap (.mach Top.loadM (stackLoadMap s)) (r.loaded s.val) (r.loaded (s.val+1)) r.loadCost := by
  have ld:=Top.load_run
    (recStream (r.nums.map (binary (r.W+1))))
    (frame (binary (r.W+1) 0)) (frame (binary (r.W+1) 0))
    (frame (binary (r.W+1) 0)) (frame (binary (r.W+1) (encS r.coefficient)))
    (frame (binary (r.W+1) 2)) (List.replicate (r.m*(r.s+1)) true)
    (List.replicate (r.s+1) true) (List.replicate r.m true)
    (List.replicate r.tuples.length true) [] r.loadCapacity
    (by unfold StackRequest.loadCapacity StackRequest.word;omega)
    (by unfold StackRequest.loadCapacity;omega)
  obtain ⟨actual,hr,hh,ht,_⟩:=ld
  have hin : (fun i:Fin 14=>(r.loaded s.val).st (stackLoadMap s i)) =
      Fin.addCases (m:=13) (n:=1) (motive:=fun _=>List Bool)
        ![frame r.word,[],[],[],[],[],[],[],[],[],[],[],[]]
        (fun _:Fin 1=>List.replicate r.loadCapacity false) := by
    funext i
    fin_cases s <;> fin_cases i <;>
      simp [StackRequest.loaded,StackRequest.lens,stackLoadMap, originalLoadMap] <;> rfl
  change run Top.loadM r.loadCost
    (Fin.addCases (m:=13) (n:=1) (motive:=fun _=>List Bool)
      ![frame r.word,[],[],[],[],[],[],[],[],[],[],[],[]]
      (fun _:Fin 1=>List.replicate r.loadCapacity false))=some actual at hr
  rw [←hin] at hr
  obtain ⟨τ,e,dock⟩:=WXExec.mach_run cap (stackLoadMap_injective s) (r.loaded s.val) (fun _=>rfl) hr
  have heq : τ=r.loaded (s.val+1) := by
    apply WState.eq
    · funext i
      by_cases hx:∃j,stackLoadMap s j=i
      · obtain ⟨j,rfl⟩:=hx
        rw [dock.sh,hh]
        rfl
      · rw [(dock.other i (by intro j h;exact hx ⟨j,h⟩)).2]
        rfl
    · funext i
      by_cases hx:∃j,stackLoadMap s j=i
      · obtain ⟨j,rfl⟩:=hx
        rw [dock.st,ht]
        fin_cases s <;> fin_cases j <;>
          norm_num [StackRequest.loaded, StackRequest.lens, stackLoadMap, originalLoadMap] <;> rfl
      · rw [(dock.other i (by intro j h;exact hx ⟨j,h⟩)).1]
        fin_cases s <;> fin_cases i <;>
          first | rfl | exact False.elim (hx (by decide))
    · exact dock.val
    · exact dock.cell
  exact e.cast cap heq le_rfl

end NearQuarticWires.StagePrint
