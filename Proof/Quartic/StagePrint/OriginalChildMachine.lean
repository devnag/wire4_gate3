import Proof.Quartic.StagePrint.FullTable
import Proof.Gates.TabMachine.CompileM14

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.TabMachine
open NearCubicGates.Close.Expand.PolyTab
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicGates.Close.WordPrograms.SInt (encS SNumOn)

/-- `imp:disjoint` and `lem:print`, paper/paper.tex: an original gate's strict target and integer weights, before all corner offsets. -/
structure OriginalChildRequest where
  W : ℕ
  weights : List ℤ
  target : ℤ
  weights_fit : 4 * totalL weights + 2 * weights.length + 4 ≤ 2 ^ W
  target_fit : target.natAbs + totalL weights < 2 ^ W

/-- `lem:print`, paper/paper.tex: the explicit original-weight and constant-word fields. -/
def OriginalChildRequest.word (r : OriginalChildRequest) : List Bool :=
  Top.loadRec (recStream (r.weights.map fun z => binary (r.W+1) (encS z)))
    (frame (binary (r.W+1) (encS r.target))) (frame (binary (r.W+1) 2))
    (frame (binary (r.W+1) 0)) (List.replicate r.weights.length true)
    (frame (binary (r.W+1) 0)) (frame (binary (r.W+1) 0))
    (frame (binary (r.W+1) 0)) (frame (binary (r.W+1) 0))
    (frame (binary (r.W+1) 0)) (frame (binary (r.W+1) 0))

/-- `lem:print`, paper/paper.tex: loading the original field record has its full physical cost. -/
def OriginalChildRequest.loadCost (r : OriginalChildRequest) : ℕ :=
  Top.loadCost (recStream (r.weights.map fun z => binary (r.W+1) (encS z)))
    (frame (binary (r.W+1) (encS r.target))) (frame (binary (r.W+1) 2))
    (frame (binary (r.W+1) 0)) (List.replicate r.weights.length true)
    (frame (binary (r.W+1) 0)) (frame (binary (r.W+1) 0))
    (frame (binary (r.W+1) 0)) (frame (binary (r.W+1) 0))
    (frame (binary (r.W+1) 0)) (frame (binary (r.W+1) 0))

/-- `lem:print`, paper/paper.tex: storage for the original field record. -/
def OriginalChildRequest.loadCapacity (r : OriginalChildRequest) : ℕ :=
  2*r.word.length+1+Top.loadChainCost
    (recStream (r.weights.map fun z => binary (r.W+1) (encS z)))
    (frame (binary (r.W+1) (encS r.target))) (frame (binary (r.W+1) 2))
    (frame (binary (r.W+1) 0)) (List.replicate r.weights.length true)
    (frame (binary (r.W+1) 0)) (frame (binary (r.W+1) 0))
    (frame (binary (r.W+1) 0)) (frame (binary (r.W+1) 0))
    (frame (binary (r.W+1) 0)) (frame (binary (r.W+1) 0))

/-- `lem:print`, paper/paper.tex: a loaded block's complete thirteen fields. -/
def OriginalChildRequest.fields (r : OriginalChildRequest) : Fin 13 → List Bool :=
  ![frame r.word,r.word,recStream (r.weights.map fun z=>binary (r.W+1) (encS z)),
    frame (binary (r.W+1) (encS r.target)),frame (binary (r.W+1) 2),
    frame (binary (r.W+1) 0),List.replicate r.weights.length true,
    frame (binary (r.W+1) 0),frame (binary (r.W+1) 0),frame (binary (r.W+1) 0),
    frame (binary (r.W+1) 0),frame (binary (r.W+1) 0),frame (binary (r.W+1) 0)]

/-- `lem:print`, paper/paper.tex: three constant field blocks initialize the signed compiler's distinct working words. -/
def originalLoadMap (s : Fin 3) (i : Fin 14) : Fin 45 :=
  if i.val=0 then 0 else if i.val=13 then ⟨40+s.val,by have:=s.isLt;omega⟩
    else ⟨13*s.val+i.val,by have:=s.isLt;have:=i.isLt;omega⟩

/-- `lem:print`, paper/paper.tex: each field block is an injection. -/
theorem originalLoadMap_injective (s : Fin 3) : Function.Injective (originalLoadMap s) := by
  intro i j h
  have hv := congrArg (fun x:Fin 45=>x.val) h
  have hi:=i.isLt
  have hj:=j.isLt
  have hs:=s.isLt
  unfold originalLoadMap at hv
  split_ifs at hv <;> apply Fin.ext <;> simp_all only [Fin.val_zero,Fin.val_mk] <;> omega

/-- `lem:print`, paper/paper.tex: the three extraction scratch tapes are bounded blank storage. -/
def OriginalChildRequest.lens (r : OriginalChildRequest) (i : Fin 45) : ℕ :=
  if 40 ≤ i.val ∧ i.val < 43 then r.loadCapacity else 0

/-- `lem:print`, paper/paper.tex: after s blocks, every original coefficient is unchanged. -/
def OriginalChildRequest.loaded (r : OriginalChildRequest) (s : ℕ) : WState 44 25 :=
  ⟨fun _=>0,fun i=>if i.val=0 then frame r.word else
    if h : 1 ≤ i.val ∧ i.val < 39 ∧ (i.val-1)/13 < s ∧ (i.val-1)%13 < 12 then
      r.fields ⟨(i.val-1)%13+1,by omega⟩
    else List.replicate (r.lens i) false,fun _=>0,false⟩

/-- `lem:print`, paper/paper.tex: the zero-block bank is the physical cold start. -/
theorem originalLoad_zero (r : OriginalChildRequest) :
    r.loaded 0 = idealStart 44 25 r.word r.lens := by
  apply WState.eq
  · rfl
  · funext i
    simp [OriginalChildRequest.loaded,idealStart]
  · rfl
  · rfl

/-- `lem:print`, paper/paper.tex: each constant field block is physically extracted, with no coefficient constructor assumption. -/
theorem originalLoad_spec (cap : ℕ) (r : OriginalChildRequest) (s : Fin 3) :
    WXExec cap (.mach Top.loadM (originalLoadMap s)) (r.loaded s.val) (r.loaded (s.val+1)) r.loadCost := by
  have ld:=Top.load_run
    (recStream (r.weights.map fun z=>binary (r.W+1) (encS z)))
    (frame (binary (r.W+1) (encS r.target))) (frame (binary (r.W+1) 2))
    (frame (binary (r.W+1) 0)) (List.replicate r.weights.length true)
    (frame (binary (r.W+1) 0)) (frame (binary (r.W+1) 0))
    (frame (binary (r.W+1) 0)) (frame (binary (r.W+1) 0))
    (frame (binary (r.W+1) 0)) (frame (binary (r.W+1) 0)) r.loadCapacity
    (by unfold OriginalChildRequest.loadCapacity OriginalChildRequest.word;omega)
    (by unfold OriginalChildRequest.loadCapacity;omega)
  obtain ⟨actual,hr,hh,ht,_⟩:=ld
  have hin : (fun i:Fin 14=>(r.loaded s.val).st (originalLoadMap s i)) =
      Fin.addCases (m:=13) (n:=1) (motive:=fun _=>List Bool)
        ![frame r.word,[],[],[],[],[],[],[],[],[],[],[],[]]
        (fun _:Fin 1=>List.replicate r.loadCapacity false) := by
    funext i
    fin_cases s <;> fin_cases i <;>
      simp [OriginalChildRequest.loaded,OriginalChildRequest.lens,originalLoadMap] <;> rfl
  change run Top.loadM r.loadCost
    (Fin.addCases (m:=13) (n:=1) (motive:=fun _=>List Bool)
      ![frame r.word,[],[],[],[],[],[],[],[],[],[],[],[]]
      (fun _:Fin 1=>List.replicate r.loadCapacity false))=some actual at hr
  rw [←hin] at hr
  obtain ⟨τ,e,dock⟩:=WXExec.mach_run cap (originalLoadMap_injective s) (r.loaded s.val) (fun _=>rfl) hr
  have heq : τ=r.loaded (s.val+1) := by
    apply WState.eq
    · funext i
      by_cases hx:∃j,originalLoadMap s j=i
      · obtain ⟨j,rfl⟩:=hx
        rw [dock.sh,hh]
        rfl
      · rw [(dock.other i (by intro j h;exact hx ⟨j,h⟩)).2]
        rfl
    · funext i
      by_cases hx:∃j,originalLoadMap s j=i
      · obtain ⟨j,rfl⟩:=hx
        rw [dock.st,ht]
        fin_cases s <;> fin_cases j <;>
          norm_num [OriginalChildRequest.loaded, OriginalChildRequest.lens, originalLoadMap] <;> rfl
      · rw [(dock.other i (by intro j h;exact hx ⟨j,h⟩)).1]
        fin_cases s <;> fin_cases i <;>
          first | rfl | exact False.elim (hx (by decide))
    · exact dock.val
    · exact dock.cell
  exact e.cast cap heq le_rfl

end NearQuarticWires.StagePrint
