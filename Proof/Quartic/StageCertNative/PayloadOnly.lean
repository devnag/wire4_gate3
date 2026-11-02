import Proof.Quartic.StageCertificateControl.PoolFlattenRun

set_option autoImplicit false

namespace NearQuarticWires.StageCertNative
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks marks_length)
open NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.CheckedPCPP
open StageCertificateControl

/-- `lem:print`, paper/paper.tex: only the
actual signed payloads are concatenated after the original counted
term loop; no source or duplicate count prefix enters the native stream. -/
noncomputable def payloadOnlyProgram (p : Program) : WMX (p.tapeCount+5) 16 :=
  .seq (.wm (NearCubicWires.WireExponent3_5.FinalPass.Hash4.wcopyR 13 15 14))
    (.seq (.wm (WM.rewind (StagePrint.poolOutput p) 15))
      (.seq (.wm (NearCubicWires.WireExponent3_5.FinalPass.Hash4.wcopyR 4 14 11))
        (.seq (copyPayloads (StagePrint.poolOutput p) (StagePrint.poolFinal p) 12 15 14)
          (.wm (emitC (StagePrint.poolFinal p) 12 false)))))

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual final cache scan copies every signed
payload once, using only the completed real count and cache cursor. -/
theorem payloadOnly_run (p : Program) (cap : ℕ) (source : List Bool)
    (cache : ℕ→List Bool) (count : ℕ) (σ : WState (p.tapeCount+5) 16)
    (hsim : SimW (StagePrint.poolState p source cache count 0) σ)
    (hfresh : σ.st (StagePrint.poolFinal p)=[])
    (hhead : σ.sh (StagePrint.poolFinal p)=0)
    (hcap : 100*((StagePrint.poolPrefix cache count).length+count+1)≤cap) :
    Runs cap (payloadOnlyProgram p) σ
      (1000*((StagePrint.poolPrefix cache count).length+count+1))
      (fun τ=>τ.st (StagePrint.poolFinal p)=frame ((List.range count).flatMap cache)) := by
  let C:=StagePrint.poolOutput p
  let O:=StagePrint.poolFinal p
  let B:=(StagePrint.poolPrefix cache count).length
  let payloads:=(List.range count).map cache
  have hCO : C≠O := by
    intro h
    have hh:=congrArg Fin.val h
    dsimp only [C,O,StagePrint.poolOutput,StagePrint.poolFinal] at hh
    omega
  have hOFresh : σ.st O=[] := hfresh
  have hOHead : σ.sh O=0 := hhead
  have hlen : payloads.length=count := by simp [payloads]
  have hframes : payloads.flatMap frame=StagePrint.poolPrefix cache count := by
    simp [payloads,StagePrint.poolPrefix,List.flatMap_map]
  have hflatten : payloads.flatten=(List.range count).flatMap cache := by
    simp only [payloads,List.flatten_eq_flatMap,List.flatMap_map,id_eq]
  have hflatLen : payloads.flatten.length=(payloads.map List.length).sum := by simp
  have hvolume : 2*payloads.flatten.length+count=B := by
    have hh (xs : List (List Bool)) : (xs.flatMap frame).length=2*xs.flatten.length+xs.length := by
      induction xs with
      | nil=>simp
      | cons x xs ih=>
        simp only [List.flatMap_cons,List.length_append,frame_length,List.flatten_cons,List.length_cons]
        omega
    have hv:=hh payloads
    rw [hframes,hlen] at hv
    exact hv.symm
  have hv (r : Fin 16) : σ.val r=if r=4 then count else if r=13 then B else 0 := by
    rw [hsim.val]
    by_cases h4:r=4
    · subst r;rfl
    · by_cases h13:r=13
      · subst r;rfl
      · have hr4:r.val≠4 := fun h=>h4 (Fin.ext h)
        have hr13:r.val≠13 := fun h=>h13 (Fin.ext h)
        simp only [StagePrint.poolState,hr4,hr13,h4,h13,if_false,ite_self]
  have hsC : σ.sh C=B := by rw [hsim.sh];rfl
  have hread (q : ℕ) : readTapeBit (σ.st C) q=readTapeBit (StagePrint.poolPrefix cache count) q :=
    (hsim.st C q).symm
  change 100*(B+count+1)≤cap at hcap
  have e1:=NearCubicWires.WireExponent3_5.FinalPass.Hash4.wcopyR_spec cap
    (13:Fin 16) 15 14 (by decide) (by decide) (by decide) σ
    (by rw [hv];rfl) (by rw [hv];rfl) (by simpa [hv] using (show B≤cap by omega))
  have hv13 : σ.val (13:Fin 16)=B := by rw [hv];rfl
  rw [hv13] at e1
  let σ1:=σ.setv 15 B
  have e2:=wrewind_spec cap C (15:Fin 16) B σ1 (by simp [σ1]) (by simp [σ1];omega)
  let σ2:=(σ1.setv 15 0).seth C (σ1.sh C-B)
  have e3:=NearCubicWires.WireExponent3_5.FinalPass.Hash4.wcopyR_spec cap
    (4:Fin 16) 14 11 (by decide) (by decide) (by decide) σ2
    (by simp [σ2,σ1,hv]) (by simp [σ2,σ1,hv]) (by simp [σ2,σ1,hv];omega)
  have hv4 : σ2.val (4:Fin 16)=count := by simp [σ2,σ1,hv]
  rw [hv4] at e3
  let σ3:=σ2.setv 14 count
  have e4:=copyPayloads_exec cap C O 12 15 14 hCO (by decide) (by decide) (by decide)
    payloads [] σ3
    (by intro q;simpa [σ3,σ2,σ1,hsC,hframes] using hread q)
    (by simp [σ3,σ2,σ1,hCO.symm,hOFresh,hOHead])
    (by simp [σ3,hlen]) (by rw [hlen];omega)
    (by simp [σ3,σ2,σ1,hv];omega)
    (by simp [σ3,σ2,σ1];omega)
  let σ4:=payloadsEnd σ3 C O 12 15 14 payloads
  have e5:=emitC_spec cap O (12:Fin 16) false σ4
    (by simp [σ4,payloadsEnd,σ3,σ2,σ1,Control.copySt,hCO.symm,hOHead,hOFresh,marks_length])
    (by simp [σ4,payloadsEnd,σ3,σ2,σ1,Control.copySt,hv,marks_length];omega)
  let last:=appendO σ4 O 12 [false]
  refine ⟨last,(WXExec.seq (WXExec.wm e1) (WXExec.seq (WXExec.wm e2)
    (WXExec.seq (WXExec.wm e3) (WXExec.seq e4 (WXExec.wm e5))))).mono ?_,?_⟩
  · omega
  · change last.st O=frame ((List.range count).flatMap cache)
    simp only [last,appendO,WState.setv_st,WState.seth_st,WState.sets_st,Function.update_self]
    simp only [σ4,payloadsEnd,WState.setv_st,Control.copySt,WState.seth_st,Function.update_self]
    simp only [σ3,σ2,σ1,WState.setv_st,WState.seth_st,hOFresh,List.nil_append]
    rw [←hflatten]
    exact (NearCubicGates.Close.Codec.frame_eq_marks _).symm

end NearQuarticWires.StageCertNative
