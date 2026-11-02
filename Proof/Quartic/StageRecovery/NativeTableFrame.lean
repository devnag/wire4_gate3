import Proof.Quartic.StagePrint.FullTable
import Proof.Gates.CounterAsm.Copy
import Proof.Gates.TabMachine.Occ

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageRecovery.NativeTableFrame
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.Expand.PolyTab
open NearCubicGates.Close.Recovery.HTParts
open NearCubicGates.Close.TabMachine

/-- `lem:print`, paper/paper.tex: the finite native table machine's complete fixed tape bank. -/
noncomputable abbrev tapes (a : WilliamsAlgorithm) : ℕ := (StagePrint.fullTablePrinter a).program.tapeCount

/-- `lem:print`, paper/paper.tex: the native table machine uses the initial bank without sharing its work tapes with the record framer. -/
def bank (a : WilliamsAlgorithm) (j : Fin (tapes a)) : Fin ((tapes a)+2) := ⟨j.val,by omega⟩

/-- `lem:print`, paper/paper.tex: the exact native table stream is the subsequent physical framer's source. -/
noncomputable def source (a : WilliamsAlgorithm) : Fin ((tapes a)+2) :=
  (bank a) (StagePrint.fullTablePrinter a).program.outputTape

/-- `lem:print`, paper/paper.tex: a fresh tape stores the outer frame around all computed table entries. -/
noncomputable def output (a : WilliamsAlgorithm) : Fin ((tapes a)+2) := ⟨(tapes a),by omega⟩

/-- `lem:print`, paper/paper.tex: the finite run ruler is separate from both the native table bank and its framed output. -/
noncomputable def ruler (a : WilliamsAlgorithm) : Fin ((tapes a)+2) := ⟨(tapes a)+1,by omega⟩

/-- `lem:print`, paper/paper.tex: the fixed positive width makes every computed table record nonempty. -/
theorem records_nonempty (r : StagePrint.TableRequest) :
    ∀ x ∈ (pvals false (StagePrint.cutTable r.matrix)).map (fun z => binary (r.q + 1) (NearCubicGates.Close.WordPrograms.SInt.encS z)), x ≠ [] := by
  intro x hx
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx
  intro he
  have hh := congrArg List.length he
  simp only [SignedSortKey.binary_length, List.length_nil] at hh
  omega

/-- `lem:print`, paper/paper.tex: the native
native table packet has its explicit final record-stream delimiter. -/
def recordBody (r : StagePrint.TableRequest) : List Bool :=
  (pvals false (StagePrint.cutTable r.matrix)).flatMap (fun z => frame (binary (r.q + 1) (NearCubicGates.Close.WordPrograms.SInt.encS z)))

/-- `lem:print`, paper/paper.tex: the record body
and its last false bit are precisely the complete native packet. -/
theorem output_eq_body (r : StagePrint.TableRequest) : r.output = recordBody r ++ [false] := by
  simp [StagePrint.TableRequest.output, recordBody, recStream, List.flatMap_map]

/-- `prop:time`, paper/paper.tex: the source machine and literal record-copy pass both contribute to the outer framing budget. -/
noncomputable def steps (a : WilliamsAlgorithm) (r : StagePrint.TableRequest) : ℕ :=
  2*(2 * StagePrint.fullTableCost a r + 2)+2+1+r.output.length*100+20

/-- `lem:print`, paper/paper.tex: the native table computation is followed by a literal record scan, with its literal final packet delimiter. -/
noncomputable def program (a : WilliamsAlgorithm) : WMX ((tapes a)+1) 2 :=
  .seq (.machZ (StagePrint.fullTablePrinter a).program.machine (bank a) (ruler a))
    (.wm (.seq (CounterAsm.frameLoop (source a) 1
      (fun b=>emitPair (output a) 0 b)) (.seq (emitPair (output a) 0 false) (emitC (output a) 0 false))))

/-- `prop:time`, paper/paper.tex: the run ruler contains only blank cells and the native table computation's full clock. -/
noncomputable def lens (a : WilliamsAlgorithm) (r : StagePrint.TableRequest) (i : Fin ((tapes a)+2)) : ℕ :=
  if i=(ruler a) then (2 * StagePrint.fullTableCost a r + 2) else 0

/-- `lem:print` and `prop:time`, paper/paper.tex: the checked native table computation is physically followed by its exact outer record frame. -/
theorem program_run (a : WilliamsAlgorithm) (r : StagePrint.TableRequest) :
    Runs (2*r.output.length+2) (program a)
      (idealStart ((tapes a)+1) 2 r.word ((lens a) r)) ((steps a) r)
      (fun τ=>τ.st (output a)=frame r.output) := by
  let σ:=idealStart ((tapes a)+1) 2 r.word ((lens a) r)
  have ht : 2≤(tapes a):=(StagePrint.fullTablePrinter a).program.twoTapes
  have hOut0 : (output a).val≠0 := by change (tapes a)≠0;omega
  have hRuler0 : (ruler a).val≠0 := by change (tapes a)+1≠0;omega
  have hRulerNe : (ruler a)≠0 := fun h=>hRuler0 (congrArg Fin.val h)
  have hOutRuler : (output a)≠(ruler a) := by
    intro h
    have hh:=congrArg Fin.val h
    change (tapes a)=(tapes a)+1 at hh
    omega
  obtain ⟨rf,hr,hout⟩:=(StagePrint.fullTablePrinter a).realizes r
  have hin : (fun j=>σ.st ((bank a) j))=(StagePrint.fullTablePrinter a).program.inputTapes r.word := by
    funext j
    simp only [σ,idealStart,bank,Fin.val_mk]
    split_ifs with hj
    · simp [RepairOrdinary.Program.inputTapes,hj]
    · have hne : (⟨j.val,by omega⟩:Fin ((tapes a)+2))≠(ruler a) := by
        intro h;have hh:=congrArg Fin.val h;have:=j.isLt
        simp only [ruler,Fin.val_mk] at hh;omega
      simp [lens,hne,RepairOrdinary.Program.inputTapes,hj]
  rw [←hin] at hr
  have hmap : Function.Injective (bank a) := by
    intro i j h
    exact Fin.ext (congrArg (fun x:Fin ((tapes a)+2)=>x.val) h)
  have hfar : ∀j,(bank a) j≠(ruler a) := by
    intro j h;have hh:=congrArg Fin.val h;have:=j.isLt
    simp only [bank,ruler,Fin.val_mk] at hh;omega
  obtain ⟨τ,e,dock⟩:=WXExec.machZ_run (cap:=2*r.output.length+2) hmap hfar σ hr
    (fun _=>rfl) (by simp [σ,idealStart,lens,hRulerNe]) rfl le_rfl
  have hs : τ.st (source a)=r.output := by
    change τ.st ((bank a) (StagePrint.fullTablePrinter a).program.outputTape)=_
    rw [dock.st,hout]
  have ho : τ.st (output a)=[] := by
    have hh:=dock.other (output a) (by
      intro j h
      have hv:=congrArg (fun x:Fin ((tapes a)+2)=>x.val) h
      have hlt:=j.isLt
      simp only [bank,output,Fin.val_mk] at hv
      omega)
    rw [hh.1]
    change (if (output a).val=0 then frame r.word else
      List.replicate ((lens a) r (output a)) false)=[]
    rw [if_neg hOut0,lens,if_neg hOutRuler]
    rfl
  have hhh : ∀i,τ.sh i=0 := by
    intro i
    by_cases hx:∃j,(bank a) j=i
    · obtain ⟨j,rfl⟩:=hx;exact dock.sh j
    · simpa only [σ,idealStart] using (dock.other i (by intro j h;exact hx ⟨j,h⟩)).2
  have hv : ∀q,τ.val q=0 := fun q=>by rw [dock.val];rfl
  have hso : (source a)≠(output a) := by
    intro h;have hh:=congrArg Fin.val h
    have:=(StagePrint.fullTablePrinter a).program.outputTape.isLt
    change (StagePrint.fullTablePrinter a).program.outputTape.val<(tapes a) at this
    change (StagePrint.fullTablePrinter a).program.outputTape.val=(tapes a) at hh
    omega
  have hbodylen : r.output.length = (recordBody r).length + 1 := by rw [output_eq_body r]; simp
  have hcopy:=CounterAsm.frameLoop_spec (cap:=2*r.output.length+2)
    hso (by decide : (0:Fin 2)≠1)
    (NearCubicGates.Close.Recovery.HTParts.emits_pair (cap:=2*r.output.length+2)
      (dst:=(output a)) (OP:=0))
    (d:=2) (by intro b;simp) [false] (by simp)
    ((pvals false (StagePrint.cutTable r.matrix)).map (fun z => binary (r.q + 1) (NearCubicGates.Close.WordPrograms.SInt.encS z))) [] τ
    (records_nonempty r)
    (by simpa [StagePrint.TableRequest.output,recordBody,recStream,List.flatMap_map] using hs)
    (hhh _) (by rw [ho,hhh];rfl) (by
      rw [hv]
      simp [StagePrint.TableRequest.output,recordBody,recStream,List.flatMap_map]
      omega)
    (by
      rw [hv]
      simp [StagePrint.TableRequest.output,recordBody,recStream,List.flatMap_map]
      omega)
  let ρ:=adv (source a) (output a) 0 1 τ
    ((recordBody r).flatMap fun b=>[true,b]) (recordBody r).length
  have hp : WExec (2*r.output.length+2)
      (CounterAsm.frameLoop (source a) 1 (fun b=>emitPair (output a) 0 b)) τ ρ
      ((recordBody r).length*57+1) := by
    simpa [ρ,StagePrint.TableRequest.output,recordBody,recStream,List.flatMap_map] using hcopy
  have hlen : ((recordBody r).flatMap fun b=>[true,b]).length=2*(recordBody r).length := by simp;omega
  have hrho : ρ.sh (output a)=(ρ.st (output a)).length := by
    rw [show ρ=adv (source a) (output a) 0 1 τ
      ((recordBody r).flatMap fun b=>[true,b]) (recordBody r).length from rfl,
      adv_sh_dst hso,adv_st_dst,ho,hhh]
    simp
  have hvalρ : ρ.val (0 : Fin 2) = 2 * (recordBody r).length := by
    change (adv (source a) (output a) 0 1 τ
      ((recordBody r).flatMap fun b => [true,b]) (recordBody r).length).val 0 = _
    rw [adv_val_OP (by decide), hv, hlen]
    omega
  have hp2 := emitPair_spec (2*r.output.length+2) (output a) (0 : Fin 2) false ρ hrho
    (by rw [hvalρ, hbodylen]; omega)
  let ρ2 := appendO ρ (output a) (0 : Fin 2) [true,false]
  have hρ2head : ρ2.sh (output a) = (ρ2.st (output a)).length := by
    simp [ρ2, appendO, hrho, List.length_append]
  have hρ2val : ρ2.val (0 : Fin 2) + 1 ≤ 2*r.output.length+2 := by
    simp [ρ2, appendO, hvalρ, hbodylen]
  have hemit := Codec.emitBit_spec (2*r.output.length+2) (output a) 0 false ρ2 hρ2head hρ2val
  refine (Runs.seqE e (Runs.of (WXExec.wm (hp.seq (hp2.seq hemit))) ?_)).cost
    (by unfold steps; rw [hbodylen]; omega)
  simp only [appendO,WState.setv_st,WState.seth_st,WState.sets_st,Function.update_self]
  rw [show ρ2 = appendO ρ (output a) (0 : Fin 2) [true,false] from rfl]
  simp only [appendO, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_self]
  rw [show ρ=adv (source a) (output a) 0 1 τ
    ((recordBody r).flatMap fun b=>[true,b]) (recordBody r).length from rfl,adv_st_dst,ho,
    output_eq_body r]
  simp [frame_eq_frameP,frameP,List.flatMap_append,List.append_assoc]

end NearQuarticWires.StageRecovery.NativeTableFrame
