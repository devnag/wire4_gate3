import Proof.Quartic.StageNativeMiddleMap.Layout

set_option autoImplicit false

namespace NearQuarticWires.StageNativeMiddleMap

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.Expand.PolyTab
open NearCubicGates.Close.WordPrograms

theorem loaded_loadMap (p : Program) (cap q : ℕ) (payload : List Bool) (count : ℕ) (j : Fin 14) :
    Fin.addCases (m:=13) (n:=1) (motive:=fun _=>List Bool)
      (fields q payload count) (fun _ : Fin 1=>List.replicate cap false) j=
      (loaded p cap q payload count).st (loadMap p j) := by
  fin_cases j <;> rfl

/-- `lem:print`, paper/paper.tex: the cold
physical eleven-field loader exposes both original encoded metadata
fields and the real framed middle input, with all heads returned. -/
theorem load_exec (p : Program) (cap q : ℕ) (payload : List Bool) (count : ℕ)
    (hc1 : 2*(StagePrint.NativeMiddle.word q payload count).length+1 ≤ cap)
    (hc2 : chainCost q payload count ≤ cap) :
    WXExec cap (.mach Top.loadM (loadMap p))
      (idealStart (p.tapeCount+19) 32 (StagePrint.NativeMiddle.word q payload count) (lens p cap))
      (loaded p cap q payload count) (loadCost q payload count) := by
  have ld:=Top.load_run (natWord q) (frame payload) (natWord count)
    [] [] [] [] [] [] [] [] cap hc1 hc2
  obtain ⟨actual,hr,hh,ht,_⟩:=ld
  let a:=idealStart (p.tapeCount+19) 32 (StagePrint.NativeMiddle.word q payload count) (lens p cap)
  have hin : (fun j : Fin 14=>a.st (loadMap p j))=
      Fin.addCases (m:=13) (n:=1) (motive:=fun _=>List Bool)
        ![frame (StagePrint.NativeMiddle.word q payload count),[],[],[],[],[],[],[],[],[],[],[],[]]
        (fun _ : Fin 1=>List.replicate cap false) := by
    funext j
    fin_cases j <;> simp [a,idealStart,loadMap,lens] <;> rfl
  change run Top.loadM (loadCost q payload count)
    (Fin.addCases (m:=13) (n:=1) (motive:=fun _=>List Bool)
      ![frame (StagePrint.NativeMiddle.word q payload count),[],[],[],[],[],[],[],[],[],[],[],[]]
      (fun _ : Fin 1=>List.replicate cap false))=some actual at hr
  rw [←hin] at hr
  obtain ⟨b,eb,hd⟩:=WXExec.mach_run cap (loadMap_injective p) a (fun _=>rfl) hr
  have he : b=loaded p cap q payload count := by
    apply WState.eq
    · funext i
      by_cases hi : i.val<14
      · let j : Fin 14:=⟨i.val,hi⟩
        have hij : loadMap p j=i := Fin.ext rfl
        rw [←hij,hd.sh,hh]
        rfl
      · have hn : ∀ j,loadMap p j≠i := by
          intro j h
          have hv:=congrArg Fin.val h
          change j.val=i.val at hv
          omega
        rw [(hd.other i hn).2]
        rfl
    · funext i
      by_cases hi : i.val<14
      · let j : Fin 14:=⟨i.val,hi⟩
        have hij : loadMap p j=i := Fin.ext rfl
        rw [←hij,hd.st,ht]
        change Fin.addCases (m:=13) (n:=1) (motive:=fun _=>List Bool)
          (fields q payload count) (fun _ : Fin 1=>List.replicate cap false) j=_
        exact loaded_loadMap p cap q payload count j
      · have hn : ∀ j,loadMap p j≠i := by
          intro j h
          have hv:=congrArg Fin.val h
          change j.val=i.val at hv
          omega
        rw [(hd.other i hn).1]
        have h0 : i≠(0 : Fin (p.tapeCount+20)) := by
          intro h
          have hv : i.val=0:=congrArg (fun x : Fin (p.tapeCount+20)=>x.val) h
          omega
        simp [a,idealStart,lens,loaded,show ¬i.val<13 by omega,
          show i.val≠13 by omega,h0]
    · exact hd.val
    · exact hd.cell
  exact eb.cast cap he le_rfl

end NearQuarticWires.StageNativeMiddleMap
