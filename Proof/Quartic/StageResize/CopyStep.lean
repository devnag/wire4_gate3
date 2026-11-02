import Proof.Quartic.StageResize.Pair

set_option autoImplicit false

namespace NearQuarticWires.StageResize

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells

/-- `lem:print`, paper/paper.tex: one pass reads
one payload bit, copies it, counts it and reads its next real marker. -/
def copyBody : St VV MM :=
  .seq (.op (.rdI t1))
    (.seq pairProgram (.seq (.op (.inc copied)) (.op (.rdI t0))))

def copyStep (a : DS VV MM) (bit marker : Bool) : DS VV MM :=
  { a with
    env := Function.update
      (Function.update (Function.update a.env t1 bit.toNat) copied (a.env copied + 1))
      t0 marker.toNat
    ip := a.ip + 2
    out := a.out ++ [true, bit] }

def copyScratch : List (Fin VV) := [t0, t1, copied]

theorem copyStep_fr (a : DS VV MM) (bit marker : Bool) :
    Fr a (copyStep a bit marker) copyScratch := by
  intro y hy
  have hh : y ≠ t0 ∧ y ≠ t1 ∧ y ≠ copied := by simpa [copyScratch] using hy
  simp only [copyStep, Function.update_of_ne hh.1, Function.update_of_ne hh.2.2,
    Function.update_of_ne hh.2.1]

/-- `lem:print` and `prop:time`, paper/paper.tex: the actual input pointer advances by two and only
one copied-bit counter is incremented. -/
theorem copyBody_run (C : Ctx) (a : DS VV MM) (hc : Cst a)
    (bit marker : Bool) (rest : List Bool)
    (hin : C.inp.drop a.ip = bit :: marker :: rest)
    (hfit : a.env copied + 1 < 2 ^ C.Wd) :
    Hs C copyBody a 10 (fun b => b = copyStep a bit marker) := by
  unfold copyBody
  refine Hs.seq (t1 := 1) (t2 := 8)
    (StageLift.readInputBit_spec C t1 a bit (marker :: rest) hin) ?_
  rintro b rfl
  have hbc : Cst ({a.set t1 bit.toNat with ip := a.ip + 1} : DS VV MM) := by
    refine ⟨?_, ?_, ?_⟩
    · simpa only [DS.set_env_ne _ _ (by decide : vZ ≠ t1)] using hc.z
    · simpa only [DS.set_env_ne _ _ (by decide : v1 ≠ t1)] using hc.one
    · simpa only [DS.set_env_ne _ _ (by decide : v2 ≠ t1)] using hc.two
  refine Hs.seq (t1 := 4) (t2 := 3)
    (pairProgram_run C _ hbc bit (by simp)) ?_
  rintro c rfl
  refine Hs.seq (t1 := 1) (t2 := 1)
    (hs_inc C copied _ (by
      simpa only [DS.set_env_ne _ _ (by decide : copied ≠ t1)] using hfit)) ?_
  rintro d rfl
  have hnext : C.inp.drop (a.ip + 1) = marker :: rest := by
    rw [← List.drop_drop, hin]
    rfl
  refine (StageLift.readInputBit_spec C t0 _ marker rest hnext).mono le_rfl ?_
  rintro e rfl
  simp [copyStep, DS.set, Function.update_of_ne (by decide : copied ≠ t1), Nat.add_assoc]

end NearQuarticWires.StageResize
