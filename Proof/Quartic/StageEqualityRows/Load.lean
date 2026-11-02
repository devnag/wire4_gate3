import Proof.Quartic.StageEqualityRows.Request

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageEqualityRows

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.Expand.PolyTab
open NearCubicGates.Close.WordPrograms
open StagePrint StagePrint.Downstream

theorem loadMap_injective : Function.Injective loadMap := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun x : Fin 16=>x.val) h

/-- `lem:print`, paper/paper.tex: the cold
field extraction loads the actual equality bytes and stride without
reading a separately provided equality count. -/
theorem load_spec (cap : ℕ) (r : NativeStreamRequest) :
    WXExec cap (.mach Top.loadM loadMap)
      (idealStart 15 24 (equalityRowsInput r) (lens r)) (loaded r) (loadCost r) := by
  have ld:=Top.load_run (stream r) (List.replicate (width r) true) (List.replicate r.fieldWidth true) [] [] [] [] [] [] [] [] (loadCapacity r)
    (by unfold loadCapacity equalityRowsInput stream width;omega)
    (by unfold loadCapacity;omega)
  obtain ⟨actual,hr,hh,ht,hs⟩:=ld
  let a:=idealStart 15 24 (equalityRowsInput r) (lens r)
  have hin : (fun j : Fin 14=>a.st (loadMap j))=
      Fin.addCases (m:=13) (n:=1) (motive:=fun _=>List Bool)
        ![frame (equalityRowsInput r),[],[],[],[],[],[],[],[],[],[],[],[]]
        (fun _ : Fin 1=>List.replicate (loadCapacity r) false) := by
    funext j
    fin_cases j <;> simp [a,idealStart,loadMap,lens] <;> rfl
  change run Top.loadM (loadCost r)
    (Fin.addCases (m:=13) (n:=1) (motive:=fun _=>List Bool)
      ![frame (equalityRowsInput r),[],[],[],[],[],[],[],[],[],[],[],[]]
      (fun _ : Fin 1=>List.replicate (loadCapacity r) false))=some actual at hr
  rw [←hin] at hr
  obtain ⟨b,eb,dock⟩:=WXExec.mach_run cap loadMap_injective a (fun _=>rfl) hr
  have hloaded (j : Fin 14) :
      (Fin.addCases (m:=13) (n:=1) (motive:=fun _=>List Bool)
        (fields r) (fun _ : Fin 1=>List.replicate (loadCapacity r) false)) j=(loaded r).st (loadMap j) := by
    fin_cases j <;> rfl
  have hb : b=(loaded r) := by
    apply WState.eq
    · funext i
      by_cases hi : i.val<14
      · let j : Fin 14:=⟨i.val,hi⟩
        have he : loadMap j=i:=Fin.ext rfl
        rw [←he,dock.sh,hh]
        rfl
      · have hn : ∀ j,loadMap j≠i := by
          intro j h
          have hv:=congrArg (fun x : Fin 16=>x.val) h
          change j.val=i.val at hv
          have hj:=j.isLt
          omega
        rw [(dock.other i hn).2]
        rfl
    · funext i
      by_cases hi : i.val<14
      · let j : Fin 14:=⟨i.val,hi⟩
        have he : loadMap j=i:=Fin.ext rfl
        rw [←he,dock.st,ht]
        change (Fin.addCases (m:=13) (n:=1) (motive:=fun _=>List Bool)
          (fields r) (fun _ : Fin 1=>List.replicate (loadCapacity r) false)) j=(loaded r).st (loadMap j)
        exact hloaded j
      · have hn : ∀ j,loadMap j≠i := by
          intro j h
          have hv:=congrArg (fun x : Fin 16=>x.val) h
          change j.val=i.val at hv
          have hj:=j.isLt
          omega
        rw [(dock.other i hn).1]
        simp [a,idealStart,lens,loaded,
          show ¬i.val<13 by omega,show i.val≠0 by omega,show i.val≠13 by omega]
        intro he
        have hv:=congrArg (fun x : Fin 16=>x.val) he
        change i.val=0 at hv
        omega
    · exact dock.val
    · exact dock.cell
  exact eb.cast cap hb le_rfl

end NearQuarticWires.StageEqualityRows
