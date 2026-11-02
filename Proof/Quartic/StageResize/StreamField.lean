import Proof.Quartic.StageResize.StreamRequest

set_option autoImplicit false

namespace NearQuarticWires.StageResize

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.Cells
open StageLift

/-- `lem:print`, paper/paper.tex: resize one raw
field inline, then read the next real source marker. -/
def streamRecordBody : St VV MM :=
  .seq (.op (.zero copied))
    (.seq copyLoop (.seq padLoop (.seq (.op (.emit false)) (.op (.rdI t0)))))

/-- `lem:print` and `prop:time`, paper/paper.tex: every iteration consumes one actual source field and
its next marker, with no count/value decoder or extra child factor. -/
theorem streamRecordBody_run (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (inputWidth outputWidth value : ℕ) (marker : Bool) (rest : List Bool)
    (hpos : 0 < inputWidth) (hfit : value < 2 ^ inputWidth)
    (hle : inputWidth ≤ outputWidth) (hcap : outputWidth < 2 ^ C.Wd)
    (hflag : a.env t0 = 1) (htarget : a.env targetWidth = outputWidth)
    (hin : C.inp.drop a.ip = framePayload (binary inputWidth value) ++ marker :: rest) :
    Hs C streamRecordBody a (12 * inputWidth + 7 * outputWidth + 20) (fun b =>
      b.env t0 = marker.toNat ∧ b.ip = a.ip + 2 * inputWidth + 1 ∧
      b.out = a.out ++ frame (binary outputWidth value) ∧
      Cst b ∧ Fr a b copyScratch) := by
  let bits := binary inputWidth value
  have hbits : bits.length = inputWidth := by simp [bits]
  have hpaylen : (framePayload bits).length = 2 * inputWidth := by
    have hh := congrArg List.length (frame_decompose bits)
    simp only [frame_length, List.length_cons, hbits] at hh
    omega
  unfold streamRecordBody
  refine Hx.hs (Hs.then (hs_zero C copied a) ?_)
  rintro d rfl n0 hn0
  have hzero : Fr a (a.set copied 0) copyScratch := Fr.set a 0 (by decide)
  have dc : Cst (a.set copied 0) := hc.of_fr hzero (by decide)
  refine Hs.then (copyLoop_run C bits (marker :: rest) (a.set copied 0) dc
    (by
      change (a.set copied 0).env t0 = (frameFlag (binary inputWidth value)).toNat
      rw [DS.set_env_ne _ _ (by decide : t0 ≠ copied), hflag,
        binary_flag_positive inputWidth value hpos]
      rfl) hin
    (by simp only [DS.set_env_self, Nat.zero_add, hbits]; exact hle.trans_lt hcap)) ?_
  rintro e ⟨_, eip, ecount, eout, ec, efr⟩ n1 hn1
  have ein : e.env copied = inputWidth := by
    rw [ecount]
    simp only [DS.set_env_self, Nat.zero_add, hbits]
  have etarget : e.env targetWidth = outputWidth := by
    rw [efr targetWidth (by decide), DS.set_env_ne _ _ (by decide : targetWidth ≠ copied), htarget]
  refine Hs.then (padLoop_run C e ec outputWidth etarget (by rw [ein]; exact hle) hcap) ?_
  rintro f ⟨_, fout, fip, fc, ffr⟩ n2 hn2
  refine Hs.then (hs_emit C false f) ?_
  rintro g rfl n3 hn3
  have hnext : C.inp.drop ({ f with out := f.out ++ [false] } : DS VV MM).ip = marker :: rest := by
    change C.inp.drop f.ip = _
    rw [fip, eip]
    change C.inp.drop (a.ip + 2 * bits.length) = _
    have hin' : C.inp.drop a.ip = framePayload bits ++ marker :: rest := hin
    rw [← List.drop_drop, hin']
    rw [show 2 * bits.length = (framePayload bits).length by omega, List.drop_left]
  refine Hs.last (readInputBit_spec C t0 _ marker rest hnext) ?_
  rintro b rfl n4 hn4
  have hpadfr : Fr e f copyScratch := ffr.weaken (by intro y hy; simp only [List.mem_singleton] at hy; subst y; decide)
  have hall : Fr a f copyScratch := hzero.trans (efr.trans hpadfr)
  have hlast : Fr f ({ ({ f with out := f.out ++ [false] } : DS VV MM).set t0 marker.toNat
      with ip := f.ip + 1 }) copyScratch := by
    intro y hy
    have hne : y ≠ t0 := by intro he; subst y; exact hy (by decide)
    exact DS.set_env_ne _ _ hne
  refine ⟨⟨?_, ?_, ?_, fc.of_fr hlast (by decide), hall.trans hlast⟩, ?_⟩
  · simp only [DS.set_env_self]
  · change f.ip + 1 = _
    rw [fip, eip]
    simp only [DS.set_ip, hbits]
  · change f.out ++ [false] = _
    rw [fout, eout, ein]
    let r : ResizeRequest := ⟨inputWidth, outputWidth, value, hfit, hle⟩
    have hh := r.output_padding
    change frame (binary outputWidth value) = Pool.fpre bits ++
      Pool.fpre (List.replicate (outputWidth - inputWidth) false) ++ [false] at hh
    rw [hh]
    simp only [DS.set_out, List.append_assoc]
  · rw [hbits] at hn1
    omega

end NearQuarticWires.StageResize
