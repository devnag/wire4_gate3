import Proof.Quartic.StageResize.PadLoop
import Proof.Quartic.StageGamma.ReadFields
import Proof.Gates.Cells.Prelude

set_option autoImplicit false

namespace NearQuarticWires.StageResize

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.Cells
open StageLift

/-- `lem:print`, paper/paper.tex: parse only the
target width, physically count/copy the actual source payload and pad. -/
def bodyProgram : St VV MM :=
  .seq (StageGamma.readField targetWidth)
    (.seq (.op (.zero copied))
      (.seq (.op (.rdI t0)) (.seq copyLoop (.seq padLoop (.op (.emit false))))))

def bodyClock (r : ResizeRequest) : ℕ :=
  30 * natBitLength r.outputWidth + 12 * r.inputWidth + 7 * r.outputWidth + 90

/-- `lem:print` and `prop:time`, paper/paper.tex: actual source parsing/copy/padding consumes the complete
request and emits exactly the desired field with one frame. -/
theorem bodyProgram_run (C : Ctx) (r : ResizeRequest) (a : DS VV MM)
    (hc : Cst a) (hin : C.inp.drop a.ip = r.word)
    (hwidth : r.outputWidth + natBitLength r.outputWidth + 4 ≤ C.Wd) :
    Hs C bodyProgram a (bodyClock r) (fun b =>
      b.out = a.out ++ r.output ∧ b.ip = a.ip + r.word.length) := by
  let bits := binary r.inputWidth r.value
  have hbits : bits.length = r.inputWidth := by simp [bits]
  change C.inp.drop a.ip = natWord r.outputWidth ++ frame bits at hin
  have hcap : r.outputWidth < 2 ^ C.Wd :=
    (show r.outputWidth ≤ C.Wd by omega).trans_lt Nat.lt_two_pow_self
  unfold bodyProgram
  refine Hx.hs (Hs.then (StageGamma.readField_spec C targetWidth (by decide) (by decide)
    a hc r.outputWidth (frame bits) hin (by omega)) ?_)
  rintro b ⟨bt, bip, brest, bc, _⟩ n0 hn0
  have bout : b.out = a.out := congrArg Prod.fst brest
  have bin : C.inp.drop b.ip = frame bits := by
    rw [bip, ← List.drop_drop, hin]
    simp
  refine Hs.then (hs_zero C copied b) ?_
  rintro c rfl n1 hn1
  have hzero : Fr b (b.set copied 0) [copied] := Fr.set b _ (by simp)
  have cc : Cst (b.set copied 0) := bc.of_fr hzero (by decide)
  have hframe : C.inp.drop (b.set copied 0).ip = frameFlag bits :: framePayload bits := by
    change C.inp.drop b.ip = _
    rw [bin, frame_decompose bits]
  refine Hs.then (readInputBit_spec C t0 _ (frameFlag bits) (framePayload bits) hframe) ?_
  rintro d0 rfl n2 hn2
  let d : DS VV MM := { (b.set copied 0).set t0 (frameFlag bits).toNat with ip := b.ip + 1 }
  have dc : Cst d := by
    refine ⟨?_, ?_, ?_⟩
    · simpa only [d, DS.set_env_ne _ _ (by decide : vZ ≠ t0)] using cc.z
    · simpa only [d, DS.set_env_ne _ _ (by decide : v1 ≠ t0)] using cc.one
    · simpa only [d, DS.set_env_ne _ _ (by decide : v2 ≠ t0)] using cc.two
  have dcount : d.env copied = 0 := by
    simp only [d, DS.set_env_ne _ _ (by decide : copied ≠ t0), DS.set_env_self]
  have dtarget : d.env targetWidth = r.outputWidth := by
    simp only [d, DS.set_env_ne _ _ (by decide : targetWidth ≠ t0),
      DS.set_env_ne _ _ (by decide : targetWidth ≠ copied), bt]
  have din : C.inp.drop d.ip = framePayload bits ++ [] := by
    change C.inp.drop (b.ip + 1) = _
    rw [← List.drop_drop, bin, frame_decompose bits]
    simp
  refine Hs.then (copyLoop_run C bits [] d dc (by simp [d]) din
    (by rw [dcount, Nat.zero_add, hbits]; exact r.width_le.trans_lt hcap)) ?_
  rintro e ⟨_, eip, ecount, eout0, ec, efr⟩ n3 hn3
  have ein : e.env copied = r.inputWidth := by rw [ecount, dcount, Nat.zero_add, hbits]
  have etarget : e.env targetWidth = r.outputWidth := by
    rw [efr targetWidth (by decide), dtarget]
  have eout : e.out = a.out ++ Pool.fpre bits := by
    rw [eout0]
    change b.out ++ Pool.fpre bits = _
    rw [bout]
  refine Hs.then (padLoop_run C e ec r.outputWidth etarget (by rw [ein]; exact r.width_le) hcap) ?_
  rintro f ⟨_, fout, fip, _, _⟩ n4 hn4
  refine Hs.last (hs_emit C false f) ?_
  rintro g rfl n5 hn5
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · change f.out ++ [false] = a.out ++ r.output
    rw [fout, eout, ein, r.output_padding]
    simp only [bits, List.append_assoc]
  · change f.ip = a.ip + r.word.length
    rw [fip, eip]
    simp only [d, bip, hbits, ResizeRequest.word, List.length_append, frame_length, binary_length]
    omega
  · unfold bodyClock
    rw [hbits] at hn3
    omega

def program : St VV MM := .seq initP bodyProgram

/-- `prop:time`, paper/paper.tex: the cold
source clock includes initialization of all arithmetic constants. -/
def sourceClock (r : ResizeRequest) : ℕ := bodyClock r + 6

/-- `lem:print`, paper/paper.tex: the actual
program starts from the zero state and emits only one framed field. -/
theorem program_run (C : Ctx) (r : ResizeRequest) (hin : C.inp = r.word)
    (hwidth : r.outputWidth + natBitLength r.outputWidth + 4 ≤ C.Wd) :
    Hs C program (a0 : DS VV MM) (sourceClock r) (fun b => b.out = r.output) := by
  have htwo : 2 < 2 ^ C.Wd := by
    have hp : 4 ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (n := 2) (by decide)
      (show 2 ≤ C.Wd by omega)
    omega
  unfold program sourceClock
  refine (Hs.seq (t1 := 5) (t2 := bodyClock r)
    (initP_spec (C := C) (a0 : DS VV MM) rfl rfl rfl htwo) ?_).mono (by omega) (fun _ h => h)
  rintro a ⟨hc, _, _, hip, hout, _, _, _, _⟩
  refine (bodyProgram_run C r a hc (by
    rw [hip]
    change C.inp.drop 0 = r.word
    rw [List.drop_zero, hin]) hwidth).mono le_rfl ?_
  rintro b ⟨hb, _⟩
  simpa only [hout, a0, List.nil_append] using hb

end NearQuarticWires.StageResize
