import Proof.Quartic.StageMain.CompactFrameStep

/-!
# Copying a finite witness frame into the compact source store

The witness of `sec:algorithm`, paper/paper.tex,
and Step 4: the copied word retains all marker and
payload bits in their original order. The certificate suffix is untouched.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Compact

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open StageLift CallSkip

theorem framePayload_length (bits : List Bool) : (framePayload bits).length = 2 * bits.length := by
  cases bits <;> simp [framePayload, frame_length]
  omega

theorem copyFrameLoop_run (C : Ctx) (bits rest : List Bool) (a : DS VV MM) (hc : Cst a)
    (hflag : a.env t0 = (frameFlag bits).toNat)
    (hin : C.inp.drop a.ip = framePayload bits ++ rest)
    (hcursor : a.rc compactStore = (a.ram compactStore).length)
    (hcap : a.env lengthCounter + 2 * bits.length < 2 ^ C.Wd) :
    Hs C (.loop (.eq t0 v1) copyFrameBody) a (11 * bits.length + 2) (fun b =>
      b.env t0 = 0 ∧ b.ip = a.ip + 2 * bits.length ∧
      b.env lengthCounter = a.env lengthCounter + 2 * bits.length ∧
      b.ram compactStore = a.ram compactStore ++ (framePayload bits).map Bool.toNat ∧
      b.rc compactStore = a.rc compactStore + 2 * bits.length ∧
      (∀ store, store ≠ compactStore → b.ram store = a.ram store ∧ b.rc store = a.rc store) ∧
      (b.out, b.kin, b.kout, b.kc) = (a.out, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b frameScratch) := by
  induction bits generalizing a with
  | nil =>
      have he : (Cnd.eq t0 v1).eval a = false := by
        simp [Cnd.eval, hflag, frameFlag, hc.one]
      refine ⟨a, 2, Ex.loopF (show t0 ≠ v1 by decide) he, by simp, ?_⟩
      exact ⟨by simpa [frameFlag] using hflag, by simp, by simp, by simp [framePayload],
        by simp, fun _ _ => ⟨rfl, rfl⟩, rfl, hc, Fr.refl _ _⟩
  | cons bit bits ih =>
      have he : (Cnd.eq t0 v1).eval a = true := by
        simp [Cnd.eval, hflag, frameFlag, hc.one]
      have hinput : C.inp.drop a.ip = bit :: frameFlag bits :: (framePayload bits ++ rest) := by
        change C.inp.drop a.ip = (bit :: frame bits) ++ rest at hin
        rw [frame_decompose bits] at hin
        simpa only [List.cons_append] using hin
      obtain ⟨b, n, hb, hn, hbeq⟩ := copyFrameBody_run C a hc bit (frameFlag bits)
        (framePayload bits ++ rest) hinput hcursor
        (by simp only [List.length_cons] at hcap; omega)
      subst b
      have hbf := frameStep_fr a bit (frameFlag bits)
      have hbc := Cst.of_fr hc hbf (by decide)
      have hbin : C.inp.drop (frameStep a bit (frameFlag bits)).ip = framePayload bits ++ rest := by
        change C.inp.drop (a.ip + 2) = _
        rw [← List.drop_drop, hinput]
        rfl
      have hblen : (frameStep a bit (frameFlag bits)).env lengthCounter = a.env lengthCounter + 2 := by
        simp [frameStep]
      have hbcur : (frameStep a bit (frameFlag bits)).rc compactStore =
          ((frameStep a bit (frameFlag bits)).ram compactStore).length := by
        simp [frameStep, hcursor]
      obtain ⟨d, k, hd, hk, hdz, hdi, hdl, hdr, hdrc, hdo, hdrest, hdc, hdf⟩ :=
        ih (frameStep a bit (frameFlag bits)) hbc
          (by simp (config := {decide := true}) [frameStep, DS.set]) hbin hbcur
          (by rw [hblen]; simp only [List.length_cons] at hcap; omega)
      refine ⟨d, n + k + 2, Ex.loopT (show t0 ≠ v1 by decide) he hb hd, by simp; omega, ?_⟩
      refine ⟨hdz, ?_, ?_, ?_, ?_, ?_, hdrest, hdc, hbf.trans hdf⟩
      · rw [hdi]
        change a.ip + 2 + 2 * bits.length = a.ip + 2 * (bit :: bits).length
        simp only [List.length_cons]
        omega
      · rw [hdl, hblen]
        simp only [List.length_cons]
        omega
      · rw [hdr]
        change (a.ram compactStore ++ [bit.toNat, (frameFlag bits).toNat]) ++
          (framePayload bits).map Bool.toNat = a.ram compactStore ++ (framePayload (bit :: bits)).map Bool.toNat
        simp only [framePayload, frame_decompose bits, List.map_cons, List.append_assoc,
          List.cons_append, List.nil_append]
      · rw [hdrc]
        simp only [frameStep, Function.update_self, List.length_cons]
        omega
      · intro other ho
        simpa only [frameStep, Function.update_of_ne ho] using hdo other ho

end NearQuarticWires.StageMain.Compact
