import Proof.Quartic.StageLift.PreparedOutput
import Proof.Quartic.StageLift.GammaWalk
import Proof.Quartic.StageLift.Token

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells

/-- Step 3 and `lem:print`, paper/paper.tex: one measured raw preparation source precedes
the actual original all-walk count and all subsequent Formula packets. -/
def emitCarrierPrefix : St VV MM :=
  .seq (StageRecovery.emitVariable preparedLength)
    (.seq emitPreparedWord (StageRecovery.emitVariable printWalkCount))

/-- Step 3 and `lem:print`, paper/paper.tex: every preparation byte and both actual count headers
are output once with all rewinds and binary serialization paid.
Neither the raw source nor its measured length is a supplied output word. -/
theorem emitCarrierPrefix_spec (C : Ctx) (bits : List Bool) (count : ℕ)
    (a : DS VV MM) (hc : Cst a)
    (hbits : a.ram preparedStore = bits.map Bool.toNat)
    (hlen : a.env preparedLength = bits.length) (hcount : a.env printWalkCount = count)
    (hfit : bits.length < 2 ^ C.Wd) (hW : 2 ≤ C.Wd)
    (hP : natBitLength bits.length + 2 < 2 ^ C.Wd)
    (hN : natBitLength count + 2 < 2 ^ C.Wd) :
    Hs C emitCarrierPrefix a
      (a.rc preparedStore + 8 * bits.length +
        40 * (natBitLength bits.length + natBitLength count) + 94) (fun b =>
      b.out = a.out ++ natWord bits.length ++ bits ++ natWord count ∧
      b.rc = Function.update a.rc preparedStore bits.length ∧
      (b.ip, b.ram, b.kin, b.kout, b.kc) = (a.ip, a.ram, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b ([c0, t0] ++ tokenScratch)) := by
  unfold emitCarrierPrefix
  have hp := StageRecovery.emitVariable_spec C a hc preparedLength (by decide) hW
    (by rw [hlen]; exact hP)
  rw [hlen] at hp
  refine (Hs.seq (t1 := 40 * natBitLength bits.length + 42)
    (t2 := a.rc preparedStore + 8 * bits.length + 6 + 40 * natBitLength count + 43) hp
    fun b ⟨hbo, hbrest, hbc, hbfr⟩ => ?_).mono (by omega) (fun _ h => h)
  have hbram : b.ram = a.ram := congrArg (fun t => t.2.1) hbrest
  have hbrc : b.rc = a.rc := congrArg (fun t => t.2.2.1) hbrest
  have hblen : b.env preparedLength = bits.length := (hbfr _ (by decide)).trans hlen
  have hbn : b.env printWalkCount = count := (hbfr _ (by decide)).trans hcount
  have he := emitPreparedWord_spec C bits b hbc (by rw [hbram]; exact hbits) hblen hfit
  rw [hbrc] at he
  refine Hs.seq (t2 := 40 * natBitLength count + 42) he
    fun d ⟨hdo, hdi, hdram, hdrc, hdcallee, hdc, hdfr⟩ => ?_
  have hdn : d.env printWalkCount = count := (hdfr _ (by decide)).trans hbn
  have hn := StageRecovery.emitVariable_spec C d hdc printWalkCount (by decide) hW
    (by rw [hdn]; exact hN)
  rw [hdn] at hn
  refine hn.mono le_rfl ?_
  rintro e ⟨heo, herest, hec, hefr⟩
  have herc : e.rc = d.rc := congrArg (fun t => t.2.2.1) herest
  have hsmall : (e.ip, e.ram, e.kin, e.kout, e.kc) = (d.ip, d.ram, d.kin, d.kout, d.kc) :=
    congrArg (fun t => (t.1, t.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2)) herest
  have hbsmall : (b.ip, b.ram, b.kin, b.kout, b.kc) = (a.ip, a.ram, a.kin, a.kout, a.kc) :=
    congrArg (fun t => (t.1, t.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2)) hbrest
  have hdsmall : (d.ip, d.ram, d.kin, d.kout, d.kc) = (b.ip, b.ram, b.kin, b.kout, b.kc) := by
    simp only [Prod.mk.injEq] at hdcallee ⊢
    exact ⟨hdi, hdram, hdcallee.1, hdcallee.2.1, hdcallee.2.2⟩
  refine ⟨?_, by rw [herc, hdrc], hsmall.trans (hdsmall.trans hbsmall), hec, ?_⟩
  · rw [heo, hdo, hbo]
  · exact (hbfr.weaken (by
      intro x hx
      simp only [tokenScratch, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hx ⊢
      tauto)).trans ((hdfr.weaken (by simp)).trans (hefr.weaken (by
        intro x hx
        simp only [tokenScratch, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hx ⊢
        tauto)))

end NearQuarticWires.StageLift
