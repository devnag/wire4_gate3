import Proof.Quartic.StageCertificateControl.NativePrefixState

/-!
# Prefix an unchanged signed native payload with retained binary bytes

Paper: `lem:print`, paper/paper.tex,
and `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks marks_length)
open NearCubicGates.Close NearCubicGates.Close.WordPrograms

/-- `lem:print` and `prop:time`, paper/paper.tex: actual marker-driven copies prefix
the retained binary header to the unchanged complete native payload.
The clock is linear in actual bytes, and no output length is inferred. -/
theorem nativePrefixEmit_exec (p : Program) (cap : ℕ) (header payload : List Bool)
    (σ : WState (p.tapeCount+11) 32)
    (hH : ∀ q,readTapeBit (σ.st (indexedExternal p 1)) (σ.sh (indexedExternal p 1)+q)=
      readTapeBit (frame header) q)
    (hB : ∀ q,readTapeBit (σ.st (indexedExternal p 2)) (σ.sh (indexedExternal p 2)+q)=
      readTapeBit (frame payload) q)
    (ho : σ.st (indexedFinal p)=[]) (hoh : σ.sh (indexedFinal p)=0)
    (h19 : σ.val 19=0) (h20 : σ.val 20=0)
    (hcap : 100*(header.length+payload.length+1)≤cap) :
    Runs cap (nativePrefixEmitProgram p) σ (100*(header.length+payload.length+1))
      (fun τ => τ.st (indexedFinal p)=frame (header++payload)) := by
  let H := indexedExternal p 1
  let B := indexedExternal p 2
  let O := indexedFinal p
  have hO : σ.st O=[] := ho
  have hOh : σ.sh O=0 := hoh
  have hHO : H≠O := (indexedFinal_fresh p).1 1
  have hBO : B≠O := (indexedFinal_fresh p).1 2
  have hBH : B≠H := by intro h;have hh := congrArg Fin.val h;change 2=1 at hh;omega
  have eh := copyPayload_exec cap σ H O 19 20 hHO (by decide) header []
    (by simpa only [List.append_nil] using hH) (by rw [hO,hOh];rfl)
    (by rw [h19];omega) (by rw [h20];omega)
  let a := (Control.copySt σ H O 19 20 header.length (marks header)).seth H
    (σ.sh H+2*header.length+1)
  have eb := copyPayload_exec cap a B O 19 20 hBO (by decide) payload []
    (by intro q;simpa [a,Control.copySt,hBH,hBO] using hB q)
    (by simp [a,Control.copySt,hHO.symm,hO,hOh,marks_length])
    (by simp [a,Control.copySt,h19,marks_length];omega)
    (by simp [a,Control.copySt,h20];omega)
  let b := (Control.copySt a B O 19 20 payload.length (marks payload)).seth B
    (a.sh B+2*payload.length+1)
  have ee := emitC_spec cap O (19 : Fin 32) false b
    (by simp [b,a,Control.copySt,hBO.symm,hHO.symm,hO,hOh,marks_length,Nat.add_assoc])
    (by simp [b,a,Control.copySt,h19,marks_length];omega)
  refine (Runs.of (eh.seq (eb.seq (WXExec.wm ee))) ?_).cost (by omega)
  change (((b.sets O (b.st O++[false])).seth O (b.sh O+1)).setv 19 (b.val 19+1)).st O=_
  simp only [WState.setv_st,WState.seth_st,WState.sets_st,Function.update_self]
  simp [b,a,Control.copySt,hO,Codec.frame_eq_marks,
    NearCubicWires.RepairOrdinary.Streaming.marks_append,List.append_assoc]

end NearQuarticWires.StageCertificateControl
