import Proof.Quartic.StageNativeKidsPool.ColdLayout
import Proof.Gates.Expand.PolyTabPack

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageNativeKidsPool
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Expand.PolyTab
open StageNativeKids

variable {Q R : Type} {input : R→List Bool}

/-- `lem:print`, paper/paper.tex: the
cold original-row pool reads exactly the original indexed source,
affine header and binary target-width field. -/
def sourceWord (F : Q→Family R input) (width : Q→ℕ) (q : Q) : List Bool:=
  poolSourceWord (F q).source (F q).header (width q)

/-- `prop:time`, paper/paper.tex: source
extraction pays the literal finite three-field record and no runtime
numeric value of the target width. -/
def loadCost (F : Q→Family R input) (width : Q→ℕ) (q : Q) : ℕ:=
  Top.loadCost (frame (F q).source) (frame (F q).header) (natWord (width q)) [] [] [] [] [] [] [] []

/-- `prop:time`, paper/paper.tex: the
fixed-loader blank capacity is charged from actual source bytes. -/
def loadCapacity (F : Q→Family R input) (width : Q→ℕ) (q : Q) : ℕ:=
  2*(sourceWord F width q).length+1+
    Top.loadChainCost (frame (F q).source) (frame (F q).header) (natWord (width q))
      [] [] [] [] [] [] [] []

/-- `lem:print`, paper/paper.tex: the
loaded finite source fields retain both original frames and the binary
width codec without a child count or row cache supplied as input. -/
def fields (F : Q→Family R input) (width : Q→ℕ) (q : Q) : Fin 13→List Bool:=
  ![frame (sourceWord F width q),sourceWord F width q,frame (F q).source,
    frame (F q).header,natWord (width q),[],[],[],[],[],[],[],[]]

/-- `prop:time`, paper/paper.tex: only
actual loader and original-counter clocks occupy initial blank rulers. -/
def lens (F : Q→Family R input) (width countBudget : Q→ℕ)
    (counter row : Program) (q : Q) (i : Fin (streams counter row+1)) : ℕ:=
  if i.val=13 then loadCapacity F width q else if i.val=16 then countBudget q else 0

/-- `lem:print`, paper/paper.tex: the
actual loaded pool state retains every original source field and its
untouched counter ruler before either compiler is called. -/
def loaded (F : Q→Family R input) (width countBudget : Q→ℕ)
    (counter row : Program) (q : Q) : WState (streams counter row) 16:=
  ⟨fun _=>0,fun i=>if h:i.val<13 then fields F width q ⟨i.val,h⟩ else
    List.replicate (lens F width countBudget counter row q i) false,fun _=>0,false⟩

/-- `lem:print`, paper/paper.tex: every
loaded source slot agrees with the actual finite loader result. -/
theorem loaded_field (F : Q→Family R input) (width countBudget : Q→ℕ)
    (counter row : Program) (q : Q) (j : Fin 14) :
    (loaded F width countBudget counter row q).st (loadMap counter row j)=
      Fin.addCases (fields F width q) (fun _ : Fin 1=>List.replicate (loadCapacity F width q) false) j := by
  refine Fin.addCases (motive:=fun j=>(loaded F width countBudget counter row q).st
    (loadMap counter row j)=Fin.addCases (fields F width q)
      (fun _ : Fin 1=>List.replicate (loadCapacity F width q) false) j)
    (fun i : Fin 13=>?_) (fun i : Fin 1=>?_) j
  · rw [Fin.addCases_left]
    simp only [loaded,loadMap,Fin.val_castAdd,Fin.val_mk,dif_pos i.isLt]
  · rw [Fin.addCases_right]
    have hi : i=0:=Fin.eq_zero i
    subst hi
    rfl

/-- `lem:print`, paper/paper.tex: the
literal fixed-loader machine really extracts all three finite source
fields into the original-row pool's concrete physical bank. -/
theorem load_spec (F : Q→Family R input) (width countBudget : Q→ℕ)
    (counter row : Program) (q : Q) (cap : ℕ) :
    WXExec cap (.mach Top.loadM (loadMap counter row))
      (idealStart (streams counter row) 16 (sourceWord F width q)
        (lens F width countBudget counter row q))
      (loaded F width countBudget counter row q) (loadCost F width q) := by
  have ld:=Top.load_run (frame (F q).source) (frame (F q).header) (natWord (width q))
    [] [] [] [] [] [] [] [] (loadCapacity F width q)
    (by unfold loadCapacity sourceWord poolSourceWord;omega) (by unfold loadCapacity;omega)
  obtain ⟨actual,hr,hh,ht,_⟩:=ld
  let σ:=idealStart (streams counter row) 16 (sourceWord F width q)
    (lens F width countBudget counter row q)
  have hin : (fun i : Fin 14=>σ.st (loadMap counter row i))=
      Fin.addCases (m:=13) (n:=1) (motive:=fun _=>List Bool)
        ![frame (sourceWord F width q),[],[],[],[],[],[],[],[],[],[],[],[]]
        (fun _ : Fin 1=>List.replicate (loadCapacity F width q) false) := by
    funext i
    fin_cases i <;> rfl
  change run Top.loadM (loadCost F width q)
    (Fin.addCases (m:=13) (n:=1) (motive:=fun _=>List Bool)
      ![frame (sourceWord F width q),[],[],[],[],[],[],[],[],[],[],[],[]]
      (fun _ : Fin 1=>List.replicate (loadCapacity F width q) false))=some actual at hr
  rw [←hin] at hr
  have hi : Function.Injective (loadMap counter row):=by
    intro i j h;apply Fin.ext;exact congrArg (fun z:Fin (streams counter row+1)=>z.val) h
  obtain ⟨τ,e,dock⟩:=WXExec.mach_run cap hi σ (fun _=>rfl) hr
  have heq : τ=loaded F width countBudget counter row q:=by
    apply WState.eq
    · funext i
      by_cases h:i.val<14
      · let j : Fin 14:=⟨i.val,h⟩
        have hj : loadMap counter row j=i:=Fin.ext rfl
        rw [←hj,dock.sh,hh]
        rfl
      · rw [(dock.other i (by intro j he;have hv:=congrArg Fin.val he;have:=j.isLt;simp only [loadMap,Fin.val_mk] at hv;omega)).2]
        rfl
    · funext i
      by_cases h:i.val<14
      · let j : Fin 14:=⟨i.val,h⟩
        have hj : loadMap counter row j=i:=Fin.ext rfl
        rw [←hj,dock.st,ht]
        exact (loaded_field F width countBudget counter row q j).symm
      · rw [(dock.other i (by intro j he;have hv:=congrArg Fin.val he;have:=j.isLt;simp only [loadMap,Fin.val_mk] at hv;omega)).1]
        simp [σ,idealStart,loaded,lens,show ¬i.val<13 by omega,show i.val≠0 by omega,
          show i≠0 by intro he;have hv:=congrArg Fin.val he;simp only [Fin.val_zero] at hv;omega]
    · exact dock.val
    · exact dock.cell
  exact e.cast cap heq le_rfl

end NearQuarticWires.StageNativeKidsPool
