import Proof.Quartic.StageCertificateControl.FramePayload
import Proof.Wire_3_5.PrimAsmParseNat

/-!
# Read and return the framed whole-test census

Paper: Step 2 of `sec:algorithm`, paper/paper.tex,
and the sequential machine bound in `prop:time`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertificateControl

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicGates.Close NearCubicGates.Close.WordPrograms

variable {ns : ℕ}

/-- `prop:time`, paper/paper.tex: the length
register is doubled by a preserved copy followed by a charged move. -/
def doubleHeaderLength : WM ns 16 :=
  .seq (NearCubicWires.WireExponent3_5.FinalPass.Hash4.wcopyR 3 0 1) (WM.move 0 3)

/-- `prop:time`, paper/paper.tex: the physical
doubling preserves every tape and every other register. -/
theorem doubleHeaderLength_spec (cap : ℕ) (σ : WState ns 16)
    (h0 : σ.val 0=0) (h1 : σ.val 1=0) (hc : 2*σ.val 3≤cap) :
    WExec cap doubleHeaderLength σ (σ.setv 3 (2*σ.val 3)) (25*σ.val 3+5) := by
  have e1 := NearCubicWires.WireExponent3_5.FinalPass.Hash4.wcopyR_spec cap
    (3 : Fin 16) 0 1 (by decide) (by decide) (by decide) σ h0 h1 (by omega)
  have e2 := wmove_spec cap (0 : Fin 16) 3 (by decide) (σ.val 3)
    (σ.setv 0 (σ.val 3)) (by simp) (by simp;omega) (by simp;omega)
  refine (WExec.seq e1 e2).cast cap ?_ (by omega)
  apply WState.eq
  · rfl
  · rfl
  · funext i
    by_cases hi3 : i=3
    · subst i;simp;omega
    · by_cases hi0 : i=0
      · subst i;simp [h0]
      · simp [Function.update_of_ne hi3,Function.update_of_ne hi0]
  · rfl

/-- `prop:time`, paper/paper.tex: the bit-length
calculation excludes the decoded count's register 14. -/
def countBitRegisters : Fin 8 ↪ Fin 16 where
  toFun := ![14,0,1,2,3,4,5,6]
  inj' := by intro i j h;fin_cases i <;> fin_cases j <;> simp_all

/-- `prop:time`, paper/paper.tex: the actual
decoded count determines the distance back to the framed header's start. -/
def returnCountHeader (out : Fin (ns+1)) : WM ns 16 :=
  .seq (bitLenM countBitRegisters)
    (.seq doubleHeaderLength (.seq doubleHeaderLength
      (.seq (.inc 3) (.seq (.inc 3) (WM.rewind out 3)))))

/-- `prop:time`, paper/paper.tex: after reading
the framed count, every scratch register and the output head are restored
by explicit instructions; the decoded count is retained. -/
theorem returnCountHeader_spec (cap : ℕ) (σ : WState ns 16)
    (out : Fin (ns+1)) (T : ℕ) (hT : σ.val 14=T)
    (h0 : σ.val 0=0) (h1 : σ.val 1=0) (h2 : σ.val 2=0)
    (h3 : σ.val 3=0) (h5 : σ.val 5=0)
    (hout : σ.sh out=4*natBitLength T+2)
    (hc : T+4*natBitLength T+4≤cap) :
    WExec cap (returnCountHeader out) σ (σ.seth out 0)
      (60*T+155*natBitLength T+100) := by
  have eb := bitLenM_spec cap countBitRegisters σ
    (by simpa [countBitRegisters] using h0)
    (by simpa [countBitRegisters] using h1)
    (by simpa [countBitRegisters] using h2)
    (by simpa [countBitRegisters] using h3)
    (by simpa [countBitRegisters] using h5)
    (by simpa [countBitRegisters,hT] using (show T+2≤cap by omega))
  change WExec cap (bitLenM countBitRegisters) σ
    (σ.setv 3 (natBitLength (σ.val 14))) (60*σ.val 14+60) at eb
  rw [hT] at eb
  let s1 := σ.setv 3 (natBitLength T)
  have e1 := doubleHeaderLength_spec cap s1 (by simp [s1,h0]) (by simp [s1,h1])
    (by simp [s1];omega)
  let s2 := s1.setv 3 (2*natBitLength T)
  have e2 := doubleHeaderLength_spec cap s2 (by simp [s2,s1,h0]) (by simp [s2,s1,h1])
    (by simp [s2];omega)
  let s3 := s2.setv 3 (4*natBitLength T)
  have e3 := WExec.inc (cap:=cap) (3 : Fin 16) s3 (by simp [s3];omega)
  let s4 := s3.setv 3 (4*natBitLength T+1)
  have e4 := WExec.inc (cap:=cap) (3 : Fin 16) s4 (by simp [s4];omega)
  let s5 := s4.setv 3 (4*natBitLength T+2)
  have er := wrewind_spec cap out (3 : Fin 16) (4*natBitLength T+2) s5
    (by simp [s5]) (by simp [s5];omega)
  have hs2 : s1.setv 3 (2*s1.val 3)=s2 := by simp [s2,s1]
  have hs3 : s2.setv 3 (2*s2.val 3)=s3 := by simp [s3,s2];congr 1;ring
  rw [hs2] at e1
  rw [hs3] at e2
  change WExec cap _ s3 s4 _ at e3
  change WExec cap _ s4 s5 _ at e4
  refine (eb.seq (e1.seq (e2.seq (e3.seq (e4.seq er))))).cast cap ?_ ?_
  · apply WState.eq
    · funext i
      by_cases hi : i=out
      · subst i;simp [s5,s4,s3,s2,s1,hout]
      · simp [s5,s4,s3,s2,s1,Function.update_of_ne hi]
    · rfl
    · funext i
      by_cases hi : i=3
      · subst i;simp [h3]
      · simp [s5,s4,s3,s2,s1,Function.update_of_ne hi]
    · rfl
  · simp [s1,s2,s3,s4,s5]
    omega

/-- `sec:algorithm`, paper/paper.tex: the whole-test
count is read from its framed binary field and the same tape is returned
to its initial head before callable-bank cleanup. -/
def readCountHeader (out : Fin (ns+1)) : WM ns 16 :=
  .seq (readNatM true out 0 1 14 2 3) (returnCountHeader out)

/-- `prop:time`, paper/paper.tex: decoding and
returning the count restores all heads and all other registers, with
explicit source work depending on the actual count. -/
theorem readCountHeader_spec (cap : ℕ) (σ : WState ns 16)
    (out : Fin (ns+1)) (T : ℕ)
    (hst : σ.st out=frame (RepairRepresentation.natWord T)) (hsh : σ.sh out=0)
    (h0 : σ.val 0=0) (h1 : σ.val 1=0) (h2 : σ.val 2=0)
    (h3 : σ.val 3=0) (h5 : σ.val 5=0) (h14 : σ.val 14=0)
    (hc : 2^(natBitLength T+1)+T+4*natBitLength T+4≤cap) :
    WExec cap (readCountHeader out) σ (σ.setv 14 T)
      ((natBitLength T+2)*(40*2^natBitLength T+40)+
        60*T+155*natBitLength T+101) := by
  have er := readNatM_spec cap true out 0 1 14 2 3
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    T [] [false] σ
    (by simpa [Codec.frame_eq_marks,NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc] using hst)
    (by simpa using hsh) h0 h1 h2 h3 (by rw [h14];omega)
  let a := (σ.seth out (4*natBitLength T+2)).setv 14 T
  simp only [List.length_nil,stp,natWord_length,h14,zero_add,if_pos trivial] at er
  have eh : 2*(2*natBitLength T+1)=4*natBitLength T+2 := by ring
  rw [eh] at er
  have hreturn : T+4*natBitLength T+4≤cap :=
    le_trans (Nat.le_add_left (T+4*natBitLength T+4) (2^(natBitLength T+1)))
      (by simpa only [Nat.add_assoc] using hc)
  have eb := returnCountHeader_spec cap a out T
    (by simp [a]) (by simp [a,h0]) (by simp [a,h1]) (by simp [a,h2])
    (by simp [a,h3]) (by simp [a,h5]) (by simp [a]) hreturn
  refine (er.seq eb).cast cap ?_ (by omega)
  apply WState.eq
  · funext i
    by_cases hi : i=out
    · subst i;simp [a,hsh]
    · simp [a,Function.update_of_ne hi]
  · rfl
  · rfl
  · rfl

end NearQuarticWires.StageCertificateControl
