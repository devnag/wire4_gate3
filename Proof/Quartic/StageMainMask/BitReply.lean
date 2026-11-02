import Proof.Quartic.StageMainMask.ReplyFrameRead

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
the exact singleton structural or predicate reply contains a marker,
one Boolean payload and the terminal delimiter, all physically read. -/
def readBitReply (dst : Fin VV) : St VV MM :=
  .seq (.op (.rdK t0)) (.seq (.op (.rdK dst)) (.op (.rdK t0)))

/-- Step 4 of `sec:algorithm` and `prop:time`, paper/paper.tex: all three actual framed reply bytes
are consumed and the original source streams and stores are retained. -/
theorem readBitReply_run (C : Ctx) (dst : Fin VV)
    (hdst : dst ∉ [vZ, v1, v2, t0]) (bit : Bool) (a : DS VV MM)
    (hc : Cst a) (ho : a.kout = frame [bit]) (hk : a.kc = 0) :
    Hs C (readBitReply dst) a 5 (fun b => b.env dst = bit.toNat ∧ b.kc = 3 ∧
      (b.ip, b.out, b.ram, b.rc, b.kin, b.kout) =
        (a.ip, a.out, a.ram, a.rc, a.kin, a.kout) ∧ Cst b ∧ Fr a b [t0, dst]) := by
  have hlen : a.kout.length = 3 := by rw [ho]; rfl
  unfold readBitReply
  refine Hs.seq (t1 := 1) (t2 := 3) (hs_rdK C t0 a (by omega)) ?_
  rintro b rfl
  refine Hs.seq (t1 := 1) (t2 := 1) (hs_rdK C dst _ (by
    change a.kc + 1 < a.kout.length; omega)) ?_
  rintro d rfl
  refine (hs_rdK C t0 _ (by change a.kc + 1 + 1 < a.kout.length; omega)).mono le_rfl ?_
  rintro e rfl
  let z := ((a.set t0 (bitOf a.kout a.kc)).set dst (bitOf a.kout (a.kc + 1))).set t0
    (bitOf a.kout (a.kc + 1 + 1))
  have hd : dst ≠ t0 := by intro h; exact hdst (by simp [h])
  have hf : Fr a z [t0, dst] :=
    (Fr.set a _ (by simp)).trans ((Fr.set _ _ (by simp)).trans (Fr.set _ _ (by simp)))
  refine ⟨?_, by change a.kc + 1 + 1 + 1 = 3; omega, rfl,
    Cst.of_fr hc hf (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hdst ⊢
      exact ⟨⟨by decide, Ne.symm hdst.1⟩, ⟨by decide, Ne.symm hdst.2.1⟩,
        ⟨by decide, Ne.symm hdst.2.2.1⟩⟩), hf⟩
  change z.env dst = _
  rw [DS.set_env_ne _ _ hd, DS.set_env_self]
  simp only [ho, hk, zero_add, bitOf, frame, List.getD_cons_succ, List.getD_cons_zero]

end NearQuarticWires.StageMainMask
