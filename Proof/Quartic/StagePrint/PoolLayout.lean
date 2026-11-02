import Proof.Quartic.StagePrint.PoolStep

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearQuarticWires.Control

/-- `lem:print`, paper/paper.tex: one fixed reusable child bank is separate from the retained source and accumulated pool. -/
def poolBank (t : ℕ) (j : Fin t) : Fin (t+6) := ⟨5+j.val,by omega⟩

/-- `lem:print`, paper/paper.tex: the original source is retained on a separate tape. -/
def poolSource (p : Program) : Fin (p.tapeCount+6) := ⟨0,by omega⟩

/-- `lem:print`, paper/paper.tex: accumulated atom child caches use a separate tape. -/
def poolOutput (p : Program) : Fin (p.tapeCount+6) := ⟨1,by omega⟩

/-- `lem:print`, paper/paper.tex: the four call registers occupy fixed scalar slots. -/
def poolSiteRegs : Fin 4 ↪ Fin 16 :=
  ⟨fun i=>⟨i.val,by have:=i.isLt;omega⟩,by intro i j h;exact Fin.ext (congrArg (fun x : Fin 16=>x.val) h)⟩

/-- `lem:print`, paper/paper.tex: indexed serialization uses eight distinct registers outside the call scratch. -/
def poolWriterRegs : Fin 8 ↪ Fin 16 :=
  ⟨fun i=>⟨4+i.val,by have:=i.isLt;omega⟩,by
    intro i j h
    apply Fin.ext
    have hh:=congrArg Fin.val h
    simp only [Fin.val_mk] at hh
    omega⟩

/-- `lem:print`, paper/paper.tex: the concrete pool caller has one work bank, tally, guard, and reset ruler. -/
def poolSite (p : Program) : Site p (p.tapeCount+5) 16 where
  bank:=poolBank p.tapeCount
  tally:=⟨2,by omega⟩
  guard:=⟨3,by omega⟩
  ruler:=⟨4,by omega⟩
  regs:=poolSiteRegs
  bank_inj:=by
    intro i j h
    apply Fin.ext
    have hh:=congrArg Fin.val h
    simp only [poolBank,Fin.val_mk] at hh
    omega
  tally_ne:=by intro j h;have hh:=congrArg Fin.val h;change 5+j.val=2 at hh;omega
  guard_ne:=by intro j h;have hh:=congrArg Fin.val h;change 5+j.val=3 at hh;omega
  ruler_ne:=by intro j h;have hh:=congrArg Fin.val h;change 5+j.val=4 at hh;omega
  tally_guard:=by have:=p.twoTapes;intro h;have hh:=congrArg Fin.val h;change 2=3 at hh;omega
  tally_ruler:=by have:=p.twoTapes;intro h;have hh:=congrArg Fin.val h;change 2=4 at hh;omega
  guard_ruler:=by have:=p.twoTapes;intro h;have hh:=congrArg Fin.val h;change 3=4 at hh;omega

/-- `lem:print`, paper/paper.tex: accumulated original-atom caches are stored as a sequential list of framed child streams. -/
def poolPrefix (cache : ℕ→List Bool) (j : ℕ) : List Bool :=
  (List.range j).flatMap (fun i=>frame (cache i))

/-- `lem:print`, paper/paper.tex: the next original occurrence appends exactly one framed child cache. -/
theorem poolPrefix_succ (cache : ℕ→List Bool) (j : ℕ) :
    poolPrefix cache (j+1)=poolPrefix cache j++frame (cache j) := by
  simp [poolPrefix,List.range_succ]

/-- `lem:print`, paper/paper.tex: the source, pool, occurrence index, and remaining count are the complete pool-loop state. -/
def poolState (p : Program) (source : List Bool) (cache : ℕ→List Bool) (j left : ℕ) :
    WState (p.tapeCount+5) 16 :=
  ⟨fun i=>if i.val=1 then (poolPrefix cache j).length else 0,
    fun i=>if i.val=0 then frame source else if i.val=1 then poolPrefix cache j else [],
    fun i=>if i.val=4 then j else if i.val=13 then (poolPrefix cache j).length else
      if i.val=14 then left else 0,false⟩

/-- `lem:print`, paper/paper.tex: every reusable child tape is physically empty at the start of the next occurrence. -/
theorem poolState_bank (p : Program) (source : List Bool) (cache : ℕ→List Bool) (j left : ℕ)
    (q : Fin p.tapeCount) :
    (poolState p source cache j left).st (poolBank p.tapeCount q)=[] ∧
      (poolState p source cache j left).sh (poolBank p.tapeCount q)=0 := by
  have h0 : 5+q.val≠0 := by omega
  have h1 : 5+q.val≠1 := by omega
  simp [poolState,poolBank,h0,h1]

/-- `lem:print`, paper/paper.tex: appending one cache and incrementing the original occurrence index agrees with the canonical next pool state. -/
theorem poolState_next (p : Program) (source : List Bool) (cache : ℕ→List Bool) (j left : ℕ) :
    (appendO (poolState p source cache j left) (poolOutput p) 13 (frame (cache j))).setv 4 (j+1)=
      poolState p source cache (j+1) left := by
  apply WState.eq
  · funext i
    by_cases hi : i=poolOutput p
    · subst hi
      simp [poolState,poolOutput,appendO,poolPrefix_succ]
    · have hv : i.val≠1 := by intro h;exact hi (Fin.ext h)
      simp only [WState.setv_sh,appendO,WState.seth_sh,WState.sets_sh]
      rw [Function.update_of_ne hi]
      simp [poolState,hv]
  · funext i
    by_cases hi : i=poolOutput p
    · subst hi
      simp [poolState,poolOutput,appendO,poolPrefix_succ]
    · have hv : i.val≠1 := by intro h;exact hi (Fin.ext h)
      simp only [WState.setv_st,appendO,WState.seth_st,WState.sets_st]
      rw [Function.update_of_ne hi]
      simp [poolState,hv]
  · funext i
    fin_cases i <;> simp [poolState,appendO,poolOutput,poolPrefix_succ]
  · rfl

end NearQuarticWires.StagePrint
