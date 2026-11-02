import Proof.Quartic.StageResize.CopyStep
import Proof.Quartic.StageResize.BinaryPadding

set_option autoImplicit false

namespace NearQuarticWires.StageResize

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.Cells
open StageLift

def copyLoop : St VV MM := .loop (.eq t0 v1) copyBody

/-- `lem:print` and `prop:time`, paper/paper.tex: consume the original frame through its delimiter,
copy exactly its marked payload and count its actual number of bits. -/
theorem copyLoop_run (C : Ctx) (bits rest : List Bool) (a : DS VV MM)
    (hc : Cst a) (hflag : a.env t0 = (frameFlag bits).toNat)
    (hin : C.inp.drop a.ip = framePayload bits ++ rest)
    (hfit : a.env copied + bits.length < 2 ^ C.Wd) :
    Hs C copyLoop a (12 * bits.length + 2) (fun b =>
      b.env t0 = 0 ∧ b.ip = a.ip + 2 * bits.length ∧
      b.env copied = a.env copied + bits.length ∧
      b.out = a.out ++ Pool.fpre bits ∧ Cst b ∧ Fr a b copyScratch) := by
  unfold copyLoop
  induction bits generalizing a with
  | nil =>
      have he : (Cnd.eq t0 v1).eval a = false := by
        simp [Cnd.eval, hflag, frameFlag, hc.one]
      refine ⟨a, 2, Ex.loopF (show t0 ≠ v1 by decide) he, by simp, ?_⟩
      exact ⟨by simpa [frameFlag] using hflag, by simp, by simp,
        by simp [Pool.fpre], hc, Fr.refl _ _⟩
  | cons bit bits ih =>
      have he : (Cnd.eq t0 v1).eval a = true := by
        simp [Cnd.eval, hflag, frameFlag, hc.one]
      have hinput : C.inp.drop a.ip = bit :: frameFlag bits :: (framePayload bits ++ rest) := by
        change C.inp.drop a.ip = (bit :: frame bits) ++ rest at hin
        rw [frame_decompose bits] at hin
        simpa only [List.cons_append] using hin
      obtain ⟨b, n, hb, hn, hbeq⟩ := copyBody_run C a hc bit (frameFlag bits)
        (framePayload bits ++ rest) hinput
        (by simp only [List.length_cons] at hfit; omega)
      subst b
      have hbf := copyStep_fr a bit (frameFlag bits)
      have hbc : Cst (copyStep a bit (frameFlag bits)) := hc.of_fr hbf (by decide)
      have hbin : C.inp.drop (copyStep a bit (frameFlag bits)).ip = framePayload bits ++ rest := by
        change C.inp.drop (a.ip + 2) = _
        rw [← List.drop_drop, hinput]
        rfl
      have hbcount : (copyStep a bit (frameFlag bits)).env copied = a.env copied + 1 := by
        simp only [copyStep, Function.update_of_ne (by decide : copied ≠ t0), Function.update_self]
      obtain ⟨d, k, hd, hk, hdz, hdi, hdl, hdo, hdc, hdf⟩ :=
        ih (copyStep a bit (frameFlag bits)) hbc
          (by simp [copyStep, t0]) hbin
          (by rw [hbcount]; simp only [List.length_cons] at hfit; omega)
      refine ⟨d, n + k + 2, Ex.loopT (show t0 ≠ v1 by decide) he hb hd,
        by simp only [List.length_cons]; omega, hdz, ?_, ?_, ?_, hdc, hbf.trans hdf⟩
      · rw [hdi]
        simp only [copyStep, List.length_cons]
        omega
      · rw [hdl, hbcount]
        simp only [List.length_cons]
        omega
      · rw [hdo]
        simp [copyStep, Pool.fpre, List.append_assoc]

end NearQuarticWires.StageResize
