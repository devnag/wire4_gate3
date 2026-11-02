import Proof.Quartic.StageCertificateControl.PoolFlatten

/-!
# Exact execution of the complete native-pool finalizer

Paper: `lem:print`, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks marks_length)
open NearCubicGates.Close NearCubicGates.Close.WordPrograms

/-- The complete cache finalization in `lem:print` and `prop:time`,
paper/paper.tex, writes the
original preparation, its actual completed test count, and every
unchanged table payload in one exact frame. Read-alike source tapes
suffice; the destination is physically fresh and the clock is linear
in cached bytes, with only a polynomial scalar-count term. -/
theorem flattenPool_run (p : Program) (cap : ℕ) (source : List Bool)
    (cache : ℕ→List Bool) (count : ℕ) (σ : WState (p.tapeCount+5) 16)
    (hsim : SimW (StagePrint.poolState p source cache count 0) σ)
    (hfresh : σ.st (StagePrint.poolFinal p)=[])
    (hhead : σ.sh (StagePrint.poolFinal p)=0)
    (hcap : flattenPoolCapacity source.length (StagePrint.poolPrefix cache count).length count≤cap) :
    Runs cap (flattenPoolProgram p) σ
      (flattenPoolCost source.length (StagePrint.poolPrefix cache count).length count)
      (fun τ => τ.st (StagePrint.poolFinal p)=frame (flattenedPoolWord source cache count)) := by
  let S := StagePrint.poolSource p
  let C := StagePrint.poolOutput p
  let O := StagePrint.poolFinal p
  let B := (StagePrint.poolPrefix cache count).length
  let payloads := (List.range count).map cache
  have hSO : S≠O := by intro h;have hh := congrArg Fin.val h;dsimp [S,O,StagePrint.poolSource,StagePrint.poolFinal] at hh;omega
  have hCO : C≠O := by
    intro h
    have hh := congrArg Fin.val h
    dsimp [C,O,StagePrint.poolOutput,StagePrint.poolFinal] at hh
    rw [Nat.mod_eq_of_lt (by omega : 1<p.tapeCount+6)] at hh
    omega
  have hSC : S≠C := by
    intro h
    have hh := congrArg Fin.val h
    dsimp [S,C,StagePrint.poolSource,StagePrint.poolOutput] at hh
    rw [Nat.mod_eq_of_lt (by omega : 1<p.tapeCount+6)] at hh
    omega
  have hOFresh : σ.st O=[] := hfresh
  have hOHead : σ.sh O=0 := hhead
  have hlen : payloads.length=count := by simp [payloads]
  have hframes : payloads.flatMap frame=StagePrint.poolPrefix cache count := by
    simp [payloads,StagePrint.poolPrefix,List.flatMap_map]
  have hflatten : payloads.flatten=(List.range count).flatMap cache := by
    have hh (xs : List ℕ) : (xs.map cache).flatten=xs.flatMap cache := by
      induction xs with
      | nil => rfl
      | cons x xs ih => simp only [List.map_cons,List.flatten_cons,List.flatMap_cons,ih]
    exact hh (List.range count)
  have hvolume : B=2*payloads.flatten.length+count := by
    have hh (xs : List (List Bool)) : (xs.flatMap frame).length=2*xs.flatten.length+xs.length := by
      induction xs with
      | nil => simp
      | cons x xs ih => simp only [List.flatMap_cons,List.length_append,frame_length,List.flatten_cons,List.length_cons];omega
    have hv := hh payloads
    rw [hframes,hlen] at hv
    exact hv
  have hflatLen : payloads.flatten.length=(payloads.map List.length).sum := by simp
  have hbits : natBitLength count≤count+1 := StagePrint.pool_index_bits count
  have hv (r : Fin 16) : σ.val r=if r=4 then count else if r=13 then B else 0 := by
    rw [hsim.val]
    by_cases hr4 : r=4
    · subst r
      rfl
    · by_cases hr13 : r=13
      · subst r
        rfl
      · have h4 : r.val≠4 := by intro h;exact hr4 (Fin.ext h)
        have h13 : r.val≠13 := by intro h;exact hr13 (Fin.ext h)
        simp only [StagePrint.poolState,h4,h13,hr4,hr13,if_false,ite_self]
  have hsS : σ.sh S=0 := by rw [hsim.sh];rfl
  have hsC : σ.sh C=B := by rw [hsim.sh];rfl
  have hreadS (q : ℕ) : readTapeBit (σ.st S) q=readTapeBit (frame source) q := by
    have hh := hsim.st S q
    exact hh.symm
  have hreadC (q : ℕ) : readTapeBit (σ.st C) q=readTapeBit (StagePrint.poolPrefix cache count) q := by
    have hh := hsim.st C q
    exact hh.symm
  change 100*(source.length+B+count+1)≤cap at hcap
  have ec := NearCubicWires.WireExponent3_5.FinalPass.Hash4.wcopyR_spec cap
    (13 : Fin 16) 15 14 (by decide) (by decide) (by decide) σ
    (by rw [hv];rfl) (by rw [hv];rfl) (by rw [hv];dsimp [B] at *;omega)
  have hv13 : σ.val (13 : Fin 16)=B := by rw [hv];rfl
  rw [hv13] at ec
  let σ1 := σ.setv 15 B
  have er := wrewind_spec cap C (15 : Fin 16) B σ1
    (by simp [σ1]) (by simp [σ1];omega)
  let σ2 := (σ1.setv 15 0).seth C (σ1.sh C-B)
  have eh := copyPayload_exec cap σ2 S O 12 15 hSO (by decide) source []
    (by intro q;simpa [σ2,σ1,hSC,hsS] using hreadS q)
    (by simp [σ2,σ1,hCO.symm,hOFresh,hOHead])
    (by simp [σ2,σ1,hv];omega) (by simp [σ2,σ1];omega)
  let σ3 := (Control.copySt σ2 S O 12 15 source.length (marks source)).seth S
    (σ2.sh S+2*source.length+1)
  have ew := writeNatM_spec cap O flattenWriterRegs σ3
    (by simp [σ3,σ2,σ1,Control.copySt,flattenWriterRegs,hv])
    (by simp [σ3,σ2,σ1,Control.copySt,flattenWriterRegs,hv])
    (by simp [σ3,σ2,σ1,Control.copySt,flattenWriterRegs,hv])
    (by simp [σ3,σ2,σ1,Control.copySt,flattenWriterRegs,hv])
    (by simp [σ3,σ2,σ1,Control.copySt,flattenWriterRegs,hv])
    (by simp [σ3,σ2,σ1,Control.copySt,flattenWriterRegs,hv])
    (by simp [σ3,σ2,σ1,Control.copySt,hSO.symm,hCO.symm,hOHead,hOFresh,marks_length])
    (by simp [σ3,σ2,σ1,Control.copySt,flattenWriterRegs,hv,marks_length];omega)
  have hwcount : σ3.val (flattenWriterRegs 0)=count := by
    simp [σ3,σ2,σ1,Control.copySt,flattenWriterRegs,hv]
  have hwout : flattenWriterRegs 7=(12 : Fin 16) := rfl
  rw [hwcount,hwout] at ew
  let σ4 := appendO σ3 O 12 (marks (NearCubicWires.RepairRepresentation.natWord count))
  have ek := NearCubicWires.WireExponent3_5.FinalPass.Hash4.wcopyR_spec cap
    (4 : Fin 16) 14 11 (by decide) (by decide) (by decide) σ4
    (by simp [σ4,σ3,σ2,σ1,appendO,Control.copySt,hv])
    (by simp [σ4,σ3,σ2,σ1,appendO,Control.copySt,hv])
    (by simp [σ4,σ3,σ2,σ1,appendO,Control.copySt,hv];omega)
  have h4 : σ4.val (4 : Fin 16)=count := by
    simp [σ4,σ3,σ2,σ1,appendO,Control.copySt,hv]
  rw [h4] at ek
  let σ5 := σ4.setv 14 count
  have ep := copyPayloads_exec cap C O 12 15 14 hCO (by decide) (by decide) (by decide)
    payloads [] σ5
    (by intro q;simpa [σ5,σ4,σ3,σ2,σ1,appendO,Control.copySt,hCO,hSC.symm,hsC,hframes] using hreadC q)
    (by simp [σ5,σ4,σ3,σ2,σ1,appendO,Control.copySt,hSO.symm,hCO.symm,hOHead,hOFresh,marks_length])
    (by simp [σ5,hlen]) (by rw [hlen];omega)
    (by simp [σ5,σ4,σ3,σ2,σ1,appendO,Control.copySt,hv,marks_length,NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length];omega)
    (by simp [σ5,σ4,σ3,σ2,σ1,appendO,Control.copySt,hv];omega)
  let σ6 := payloadsEnd σ5 C O 12 15 14 payloads
  have ee := emitC_spec cap O (12 : Fin 16) false σ6
    (by simp [σ6,payloadsEnd,σ5,σ4,σ3,σ2,σ1,appendO,Control.copySt,hSO.symm,hCO.symm,hOHead,hOFresh,marks_length,Nat.add_assoc])
    (by simp [σ6,payloadsEnd,σ5,σ4,σ3,σ2,σ1,appendO,Control.copySt,hv,marks_length,NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.natWord_length];omega)
  have all := WXExec.seq (WXExec.wm ec) (WXExec.seq (WXExec.wm er)
    (WXExec.seq eh (WXExec.seq (WXExec.wm ew) (WXExec.seq (WXExec.wm ek)
      (WXExec.seq ep (WXExec.wm ee))))))
  refine (Runs.of all ?_).cost ?_
  · change (((σ6.sets O (σ6.st O++[false])).seth O (σ6.sh O+1)).setv 12 (σ6.val 12+1)).st O=
      frame (flattenedPoolWord source cache count)
    simp only [WState.setv_st,WState.seth_st,WState.sets_st,Function.update_self]
    simp [σ6,payloadsEnd,σ5,σ4,σ3,σ2,σ1,appendO,Control.copySt,hOFresh,
      Codec.frame_eq_marks,flattenedPoolWord,NearCubicWires.RepairOrdinary.Streaming.marks_append,
      hflatten,List.append_assoc]
  · unfold flattenPoolCost
    have hm := Nat.mul_le_mul_right (100*count+200) (Nat.add_le_add_right hbits 10)
    dsimp [B] at hvolume ⊢
    nlinarith

end NearQuarticWires.StageCertificateControl
