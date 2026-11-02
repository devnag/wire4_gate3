import Proof.Gates.Cells.Kit

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells

/-- `sec:algorithm` and `lem:print`, paper/paper.tex: the first marker of a retained framed word. -/
def frameFlag (bits : List Bool) : Bool := !bits.isEmpty

/-- `sec:algorithm` and `lem:print`, paper/paper.tex: the framed suffix after its first marker is consumed. -/
def framePayload : List Bool → List Bool
  | [] => []
  | bit :: bits => bit :: frame bits

/-- `sec:algorithm`, paper/paper.tex: every frame
has exactly one leading marker, including the empty retained prefix. -/
theorem frame_decompose (bits : List Bool) : frame bits = frameFlag bits :: framePayload bits := by
  cases bits <;> rfl

/-- `lem:print`, paper/paper.tex: one original
source bit is decoded by the actual input instruction. -/
theorem readInputBit_spec (C : Ctx) (x : Fin VV) (a : DS VV MM)
    (bit : Bool) (rest : List Bool) (hin : C.inp.drop a.ip = bit :: rest) :
    Hs C (.op (.rdI x)) a 1
      (fun b => b = { a.set x bit.toNat with ip := a.ip + 1 }) := by
  have hnonempty : 0 < (C.inp.drop a.ip).length := by rw [hin]; simp
  have hbound : a.ip < C.inp.length := by simp only [List.length_drop] at hnonempty; omega
  have hbit : bitOf C.inp a.ip = bit.toNat := by
    have h := bitOf_drop (cw := C.inp) (cp := a.ip) (u := [bit])
      (rest := rest) (by simpa using hin) 0 (by simp)
    simpa using h
  simpa only [hbit] using hs_rdI C x a hbound

/-- `sec:algorithm` and `lem:print`, paper/paper.tex: one marked payload bit is retained as a binary record,
then the next source marker is read physically. -/
def frameReadBody (store : Fin MM) : St VV MM :=
  .seq (.op (.rdI t1)) (.seq (.op (.wrM store t1)) (.op (.rdI t0)))

/-- `sec:algorithm` and `lem:print`, paper/paper.tex: the exact retained-bit and marker state after one pass. -/
def frameReadStep (a : DS VV MM) (store : Fin MM) (bit marker : Bool) : DS VV MM :=
  { a with
    env := Function.update (Function.update a.env t1 bit.toNat) t0 marker.toNat
    ip := a.ip + 2
    ram := Function.update a.ram store (a.ram store ++ [bit.toNat])
    rc := Function.update a.rc store (a.rc store + 1) }

/-- `sec:algorithm` and `lem:print`, paper/paper.tex: framed source retention charges both reads and the
actual record-store write without supplying any decoded payload. -/
theorem frameReadBody_spec (C : Ctx) (store : Fin MM) (a : DS VV MM)
    (bit marker : Bool) (rest : List Bool)
    (hin : C.inp.drop a.ip = bit :: marker :: rest)
    (hcursor : a.rc store = (a.ram store).length) :
    Hs C (frameReadBody store) a 5 (fun b => b = frameReadStep a store bit marker) := by
  unfold frameReadBody
  refine Hs.seq (t2 := 3) (readInputBit_spec C t1 a bit (marker :: rest) hin) fun b hb => ?_
  subst b
  refine Hs.seq (t2 := 1) (hs_wrM C store t1 _ hcursor.le) fun b hb => ?_
  subst b
  have hnext : C.inp.drop
      (({ a.set t1 bit.toNat with ip := a.ip + 1 } : DS VV MM).put store bit.toNat).ip =
      marker :: rest := by
    change C.inp.drop (a.ip + 1) = _
    rw [← List.drop_drop, hin]
    rfl
  refine (readInputBit_spec C t0 _ marker rest hnext).mono le_rfl ?_
  rintro b rfl
  simp [frameReadStep, DS.put, DS.set, putAt, hcursor, Nat.add_assoc]

end NearQuarticWires.StageLift
