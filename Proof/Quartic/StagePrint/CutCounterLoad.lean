import Proof.Quartic.StagePrint.CutCounterRequest

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StagePrint.CutCounter

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.Expand.PolyTab
open NearCubicGates.Close.WordPrograms

theorem loadMap_injective : Function.Injective loadMap := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun x : Fin 16=>x.val) h

/-- `lem:print`, paper/paper.tex: the cold
field extraction loads the actual equality bytes and stride without
reading a separately provided equality count. -/
theorem load_spec (cap : ℕ) (r : Request) :
    WXExec cap (.mach Top.loadM loadMap)
      (idealStart 15 24 r.word r.lens) r.loaded r.loadCost := by
  have ld:=Top.load_run r.stream r.unaryStride [] [] [] [] [] [] [] [] [] r.loadCapacity
    (by unfold Request.loadCapacity Request.word;omega)
    (by unfold Request.loadCapacity;omega)
  obtain ⟨actual,hr,hh,ht,hs⟩:=ld
  let a:=idealStart 15 24 r.word r.lens
  have hin : (fun j : Fin 14=>a.st (loadMap j))=
      Fin.addCases (m:=13) (n:=1) (motive:=fun _=>List Bool)
        ![frame r.word,[],[],[],[],[],[],[],[],[],[],[],[]]
        (fun _ : Fin 1=>List.replicate r.loadCapacity false) := by
    funext j
    fin_cases j <;> simp [a,idealStart,loadMap,Request.lens] <;> rfl
  change run Top.loadM r.loadCost
    (Fin.addCases (m:=13) (n:=1) (motive:=fun _=>List Bool)
      ![frame r.word,[],[],[],[],[],[],[],[],[],[],[],[]]
      (fun _ : Fin 1=>List.replicate r.loadCapacity false))=some actual at hr
  rw [←hin] at hr
  obtain ⟨b,eb,dock⟩:=WXExec.mach_run cap loadMap_injective a (fun _=>rfl) hr
  have hloaded (j : Fin 14) :
      (Fin.addCases (m:=13) (n:=1) (motive:=fun _=>List Bool)
        r.fields (fun _ : Fin 1=>List.replicate r.loadCapacity false)) j=r.loaded.st (loadMap j) := by
    fin_cases j <;> rfl
  have hb : b=r.loaded := by
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
          r.fields (fun _ : Fin 1=>List.replicate r.loadCapacity false)) j=r.loaded.st (loadMap j)
        exact hloaded j
      · have hn : ∀ j,loadMap j≠i := by
          intro j h
          have hv:=congrArg (fun x : Fin 16=>x.val) h
          change j.val=i.val at hv
          have hj:=j.isLt
          omega
        rw [(dock.other i hn).1]
        simp [a,idealStart,Request.lens,Request.loaded,
          show ¬i.val<13 by omega,show i.val≠0 by omega,show i.val≠13 by omega]
        intro he
        have hv:=congrArg (fun x : Fin 16=>x.val) he
        change i.val=0 at hv
        omega
    · exact dock.val
    · exact dock.cell
  exact eb.cast cap hb le_rfl

end NearQuarticWires.StagePrint.CutCounter
