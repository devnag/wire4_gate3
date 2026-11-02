import Proof.Quartic.StagePrintTuple.NaturalsCopy
import Proof.Quartic.Control.Request
import Proof.Gates.Codec.Frame

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKids

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.Recovery.HTParts
open StageTuple Control

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: the
actual nine-field affine suffix and three raw corner flags are copied
into one retained header frame without decoding their numeric values. -/
def copyHeaderProgram (src dst : Fin (ns + 1)) (OP SC K : Fin nr) : WMX ns nr :=
  .seq (.wm (copyNaturalFields 9 src dst OP SC K))
    (.seq (incTimes K 3)
      (.seq (.wm (Codec.frameStream src dst OP K))
        (.seq (.wm (emitC dst OP false))
          (.seq (.wm (WM.rewind dst OP)) (.wm (WM.clear SC))))))

/-- `prop:time`, paper/paper.tex: the
complete affine-header copy, marker emission and cursor and scratch
returns have a linear clock in the actual encoded header bytes. -/
def copyHeaderClock (values : List ℕ) (flags : List Bool) : ℕ :=
  1000 * ((values.flatMap natWord ++ flags).length + 1)

/-- `lem:print` and `prop:time`, paper/paper.tex: from the actual role suffix, the physical
copy prints the exact retained affine header, preserving every other
register and tape. Its one-use source cursor advances past the header;
the reusable retained header output has zero cursor and scratch. -/
theorem copyHeaderProgram_spec (cap : ℕ) (src dst : Fin (ns + 1)) (OP SC K : Fin nr)
    (hsd : src ≠ dst) (hOS : OP ≠ SC) (hKO : K ≠ OP) (hKS : K ≠ SC)
    (values : List ℕ) (flags pre rest : List Bool) (hlen : values.length = 9)
    (hflags : flags.length = 3) (σ : WState ns nr)
    (hs : σ.st src = pre ++ values.flatMap natWord ++ flags ++ rest)
    (hsh : σ.sh src = pre.length) (hd : σ.st dst = []) (hdh : σ.sh dst = 0)
    (hOP : σ.val OP = 0) (hSC : σ.val SC = 0) (hK : σ.val K = 0)
    (hcap : 2 * (values.flatMap natWord ++ flags).length + 10 ≤ cap) :
    ∃ τ, WXExec cap (copyHeaderProgram src dst OP SC K) σ τ (copyHeaderClock values flags) ∧
      τ = (σ.sets dst (frame (values.flatMap natWord ++ flags))).seth src
        (pre.length + (values.flatMap natWord ++ flags).length) := by
  have hc := hcap
  simp only [List.length_append, hflags] at hc
  have hframe : (frame (values.flatMap natWord ++ flags)).length =
      2 * (values.flatMap natWord).length + 2 * flags.length + 1 := by
    rw [NearCubicWires.RepairOrdinary.frame_length, List.length_append]
    omega
  have hframeCap : (frame (values.flatMap natWord ++ flags)).length ≤ cap := by omega
  have e1 := copyNaturalFields_spec cap src dst OP SC K hsd hOS hKO hKS
    values pre (flags ++ rest) σ (by simpa only [List.append_assoc] using hs) hsh
    (by rw [hdh, hd]; rfl) hK (by rw [hOP]; omega) (by rw [hSC]; omega)
  rw [hlen] at e1
  let s1 := adv src dst OP SC σ (marks (values.flatMap natWord)) (values.flatMap natWord).length
  have hk1 : s1.val K = 0 := by rw [adv_val_other _ _ _ K hKO hKS, hK]
  have e2 := incTimes_exec cap K 3 s1 (by rw [hk1]; omega)
  rw [hk1, Nat.zero_add] at e2
  let s2 := s1.setv K 3
  have e3 := Codec.frameStream_spec cap src dst hsd OP K hKO flags
    (pre ++ values.flatMap natWord) rest s2
    (by simp only [s2, WState.setv_st, s1, adv_st_src hsd]; rw [hs, List.append_assoc])
    (by simp [s2, s1, adv_sh_src, hsh])
    (by simp [s2, s1, adv, appendO, hsd.symm, hdh, hd])
    (by simp [s2, hflags]) (by omega)
    (by simp only [s2, WState.setv_val, Function.update_of_ne hKO.symm,
        s1, adv_val_OP hOS, hOP, Nat.zero_add, Codec.marks_length]; omega)
  let s3 := ((appendO s2 dst OP (marks flags)).setv K 0).seth src
    ((pre ++ values.flatMap natWord).length + flags.length)
  have e4 := Codec.emitBit_spec cap dst OP false s3
    (by simp [s3, s2, s1, adv, appendO, hsd.symm, hd, hdh, List.length_append])
    (by simp only [s3, WState.seth_val, WState.setv_val,
        appendO_val, Function.update_self, s2, WState.setv_val,
        Function.update_of_ne hKO.symm, s1, adv_val_OP hOS, hOP, Nat.zero_add,
        Codec.marks_length, hflags]; omega)
  let s4 := appendO s3 dst OP [false]
  have hop4 : s4.val OP = (frame (values.flatMap natWord ++ flags)).length := by
    simp only [s4, s3, s2, s1, WState.seth_val, WState.setv_val,
      appendO_val, Function.update_self, Function.update_of_ne hKO.symm,
      adv_val_OP hOS, hOP, Nat.zero_add, Codec.marks_length, List.length_singleton]
    omega
  have e5 := wrewind_spec cap dst OP (frame (values.flatMap natWord ++ flags)).length s4
    hop4 (by rw [hop4]; exact hframeCap)
  let s5 := (s4.setv OP 0).seth dst (s4.sh dst - (frame (values.flatMap natWord ++ flags)).length)
  have hsc5 : s5.val SC = (values.flatMap natWord).length := by
    simp [s5, s4, s3, s2, s1, adv, appendO, hOS.symm, hKS.symm, hSC]
  have e6 := wclear_spec cap SC (values.flatMap natWord).length s5 hsc5
    (by rw [hsc5]; omega)
  refine ⟨_, (WXExec.seq (.wm e1) (WXExec.seq e2 (WXExec.seq (.wm e3)
    (WXExec.seq (.wm e4) (WXExec.seq (.wm e5) (.wm e6)))))).mono ?_, ?_⟩
  · unfold copyHeaderClock
    simp only [List.length_append, hflags]
    omega
  · apply WState.eq
    · funext i
      by_cases hi : i = src
      · subst hi
        simp [s5, s4, s3, s2, s1, adv, appendO, hsd, hsh, List.length_append, Nat.add_assoc]
      · by_cases hid : i = dst
        · subst hid
          simp [s5, s4, s3, s2, s1, adv, appendO, hsd.symm, hdh,
            List.length_append]
          omega
        · simp [s5, s4, s3, s2, s1, adv, appendO, hi, hid]
    · funext i
      by_cases hi : i = dst
      · subst hi
        simp [s5, s4, s3, s2, s1, adv, appendO, hd,
          Codec.frame_eq_marks, Streaming.marks_append, List.append_assoc]
      · simp [s5, s4, s3, s2, s1, adv, appendO, hi]
    · funext i
      by_cases hi : i = OP
      · subst hi; simp [s5, hOS, hOP]
      · by_cases his : i = SC
        · subst his; simp [hSC]
        · by_cases hik : i = K
          · subst hik; simp [s5, s4, s3, s2, s1, adv, appendO, hKO, hKS, hK]
          · simp [s5, s4, s3, s2, s1, adv, appendO, hi, his, hik]
    · rfl

end NearQuarticWires.StageNativeKids
