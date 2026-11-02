import Proof.Quartic.StageCertificateControl.IndexedThreshold

/-!
# Emit the exact original-source whole-test preprocessing payload

Paper: Step 2 of `sec:algorithm`, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks marks_length marks_append)
open NearCubicGates.Close NearCubicGates.Close.WordPrograms

/-- `sec:algorithm` and `prop:time`, paper/paper.tex: the final physical preprocessing copy
retains the exact threshold, original preparation, and actual selected
metadata. It requires only their read bits and an untouched fresh
output, so it applies after the actual erased-bank computations. -/
theorem indexedEmit_exec (p : Program) (cap : ℕ) (header prep metadata : List Bool)
    (σ : WState (p.tapeCount+11) 32)
    (hH : ∀ q,readTapeBit (σ.st (indexedExternal p 6)) (σ.sh (indexedExternal p 6)+q)=
      readTapeBit (frame header) q)
    (hS : ∀ q,readTapeBit (σ.st (indexedExternal p 0)) (σ.sh (indexedExternal p 0)+q)=
      readTapeBit (frame prep) q)
    (hM : ∀ q,readTapeBit (σ.st (indexedExternal p 4)) (σ.sh (indexedExternal p 4)+q)=
      readTapeBit (frame metadata) q)
    (ho : σ.st (indexedFinal p)=[]) (hoh : σ.sh (indexedFinal p)=0)
    (h19 : σ.val 19=0) (h20 : σ.val 20=0)
    (hcap : 100*(header.length+prep.length+metadata.length+1)≤cap) :
    Runs cap (indexedEmitProgram p) σ (100*(header.length+prep.length+metadata.length+1))
      (fun τ => τ.st (indexedFinal p)=frame (header++prep++metadata)) := by
  let H := indexedExternal p 6
  let S := indexedExternal p 0
  let M := indexedExternal p 4
  let O := indexedFinal p
  have hO : σ.st O=[] := ho
  have hOh : σ.sh O=0 := hoh
  have hf := (indexedFinal_fresh p).1
  have hHO : H≠O := hf 6
  have hSO : S≠O := hf 0
  have hMO : M≠O := hf 4
  have hSH : S≠H := by intro h;have hh := congrArg Fin.val h;change 0=6 at hh;omega
  have hMH : M≠H := by intro h;have hh := congrArg Fin.val h;change 4=6 at hh;omega
  have hMS : M≠S := by intro h;have hh := congrArg Fin.val h;change 4=0 at hh;omega
  have eh := copyPayload_exec cap σ H O 19 20 hHO (by decide) header []
    (by simpa only [List.append_nil] using hH) (by rw [hO,hOh];rfl)
    (by rw [h19];omega) (by rw [h20];omega)
  let a := (Control.copySt σ H O 19 20 header.length (marks header)).seth H
    (σ.sh H+2*header.length+1)
  have es := copyPayload_exec cap a S O 19 20 hSO (by decide) prep []
    (by intro q;simpa [a,Control.copySt,hSH,hSO] using hS q)
    (by simp [a,Control.copySt,hHO.symm,hOh,hO,marks_length,Nat.add_assoc])
    (by simp [a,Control.copySt,h19,marks_length];omega)
    (by simp [a,Control.copySt,h20];omega)
  let b := (Control.copySt a S O 19 20 prep.length (marks prep)).seth S
    (a.sh S+2*prep.length+1)
  have em := copyPayload_exec cap b M O 19 20 hMO (by decide) metadata []
    (by intro q;simpa [b,a,Control.copySt,hMS,hMH,hMO] using hM q)
    (by simp [b,a,Control.copySt,hSO.symm,hHO.symm,hOh,hO,marks_length,Nat.add_assoc])
    (by simp [b,a,Control.copySt,h19,marks_length];omega)
    (by simp [b,a,Control.copySt,h20];omega)
  let c := (Control.copySt b M O 19 20 metadata.length (marks metadata)).seth M
    (b.sh M+2*metadata.length+1)
  have ee := emitC_spec cap O (19 : Fin 32) false c
    (by simp [c,b,a,Control.copySt,hMO.symm,hSO.symm,hHO.symm,hOh,hO,marks_length,Nat.add_assoc])
    (by simp [c,b,a,Control.copySt,h19,marks_length];omega)
  refine (Runs.of (eh.seq (es.seq (em.seq (WXExec.wm ee)))) ?_).cost (by omega)
  change (((c.sets O (c.st O++[false])).seth O (c.sh O+1)).setv 19 (c.val 19+1)).st O=_
  simp only [WState.setv_st,WState.seth_st,WState.sets_st,Function.update_self]
  simp [c,b,a,Control.copySt,hO,Codec.frame_eq_marks,
    NearCubicWires.RepairOrdinary.Streaming.marks_append,List.append_assoc]

end NearQuarticWires.StageCertificateControl
