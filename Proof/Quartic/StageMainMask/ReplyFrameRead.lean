import Proof.Quartic.StageLift.FrameRead

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open StageLift

/-- `lem:print`, paper/paper.tex: one original
source bit is decoded by the actual input instruction. -/
theorem readReplySourceBit_spec (C : Ctx) (x : Fin VV) (a : DS VV MM)
    (bit : Bool) (rest : List Bool) (hin : a.kout.drop a.kc = bit :: rest) :
    Hs C (.op (.rdK x)) a 1
      (fun b => b = { a.set x bit.toNat with kc := a.kc + 1 }) := by
  have hnonempty : 0 < (a.kout.drop a.kc).length := by rw [hin]; simp
  have hbound : a.kc < a.kout.length := by simp only [List.length_drop] at hnonempty; omega
  have hbit : bitOf a.kout a.kc = bit.toNat := by
    have h := bitOf_drop (cw := a.kout) (cp := a.kc) (u := [bit])
      (rest := rest) (by simpa using hin) 0 (by simp)
    simpa using h
  simpa only [hbit] using hs_rdK C x a hbound

/-- `sec:algorithm` and `lem:print`, paper/paper.tex: one marked payload bit is retained as a binary record,
then the next source marker is read physically. -/
def replyReadBody (store : Fin MM) : St VV MM :=
  .seq (.op (.rdK t1)) (.seq (.op (.wrM store t1)) (.op (.rdK t0)))

/-- `sec:algorithm` and `lem:print`, paper/paper.tex: the exact retained-bit and marker state after one pass. -/
def replyReadStep (a : DS VV MM) (store : Fin MM) (bit marker : Bool) : DS VV MM :=
  { a with
    env := Function.update (Function.update a.env t1 bit.toNat) t0 marker.toNat
    kc := a.kc + 2
    ram := Function.update a.ram store (a.ram store ++ [bit.toNat])
    rc := Function.update a.rc store (a.rc store + 1) }

/-- `sec:algorithm` and `lem:print`, paper/paper.tex: framed source retention charges both reads and the
actual record-store write without supplying any decoded payload. -/
theorem replyReadBody_spec (C : Ctx) (store : Fin MM) (a : DS VV MM)
    (bit marker : Bool) (rest : List Bool)
    (hin : a.kout.drop a.kc = bit :: marker :: rest)
    (hcursor : a.rc store = (a.ram store).length) :
    Hs C (replyReadBody store) a 5 (fun b => b = replyReadStep a store bit marker) := by
  unfold replyReadBody
  refine Hs.seq (t2 := 3) (readReplySourceBit_spec C t1 a bit (marker :: rest) hin) fun b hb => ?_
  subst b
  refine Hs.seq (t2 := 1) (hs_wrM C store t1 _ hcursor.le) fun b hb => ?_
  subst b
  have hnext : (({ a.set t1 bit.toNat with kc := a.kc + 1 } : DS VV MM).put store bit.toNat).kout.drop
      (({ a.set t1 bit.toNat with kc := a.kc + 1 } : DS VV MM).put store bit.toNat).kc =
      marker :: rest := by
    change a.kout.drop (a.kc + 1) = _
    rw [← List.drop_drop, hin]
    rfl
  refine (readReplySourceBit_spec C t0 _ marker rest hnext).mono le_rfl ?_
  rintro b rfl
  simp [replyReadStep, DS.put, DS.set, putAt, hcursor, Nat.add_assoc]

end NearQuarticWires.StageMainMask
