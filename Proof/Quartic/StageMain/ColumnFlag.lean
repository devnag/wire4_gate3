import Proof.Quartic.StageMain.Totals
import Proof.Quartic.StageMain.CertifiedScanBuilder

/-!
# Reading the actual certificate bit of a column

Step 4 of `sec:algorithm`, paper/paper.tex,
visits columns in their literal bitmap order. Two input operations
consume a frame marker and its certified-column bit, preserving the
retained coefficients, both totals and every record store.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Controller

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells

def readColumnFlag : St VV MM := .seq (.op (.rdI t0)) (.op (.rdI certifiedFlag))

def columnFlagScratch : List (Fin VV) := [t0, certifiedFlag]

theorem readColumnFlag_run (C : Ctx) (bits rest : List Bool) (base i : ℕ)
    (hi : i < bits.length) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop base = frame bits ++ rest) (hip : a.ip = base + 2 * i) :
    Hs C readColumnFlag a 3 (fun b =>
      b.env certifiedFlag = (bits[i]).toNat ∧ b.ip = base + 2 * (i + 1) ∧
      (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.out, a.ram, a.rc, a.kin, a.kout, a.kc) ∧ Cst b ∧
      Fr a b columnFlagScratch) := by
  have hlen : (frame bits).length = 2 * bits.length + 1 := frame_length bits
  have hread0 : a.ip < C.inp.length := by
    rw [hip]; exact lt_of_drop hin (2 * i) (by rw [hlen]; omega)
  have hread1 : a.ip + 1 < C.inp.length := by
    rw [hip, Nat.add_assoc]; exact lt_of_drop hin (2 * i + 1) (by rw [hlen]; omega)
  have hbit : bitOf C.inp (a.ip + 1) = (bits[i]).toNat := by
    rw [hip, Nat.add_assoc, bitOf_drop hin (2 * i + 1) (by rw [hlen]; omega)]
    rw [frame_getD_odd, List.getD_eq_getElem _ _ hi]
  unfold readColumnFlag
  refine Hs.seq (t1 := 1) (t2 := 1) (hs_rdI C t0 a hread0) ?_
  rintro b rfl
  refine (hs_rdI C certifiedFlag _ hread1).mono le_rfl ?_
  rintro d rfl
  have hf : Fr a ((a.set t0 (bitOf C.inp a.ip)).set certifiedFlag (bitOf C.inp (a.ip + 1)))
      columnFlagScratch :=
    (Fr.set a _ (by simp [columnFlagScratch])).trans
      (Fr.set _ _ (by simp [columnFlagScratch]))
  exact ⟨hbit, by dsimp; omega, rfl, Cst.of_fr hc hf (by decide), hf⟩

theorem readCertifiedFlag_run (C : Ctx) (c : Algorithm.CellCall) (rest : List Bool)
    (base : ℕ) (z : Fin c.ncol) (a : DS VV MM) (hc : Cst a)
    (hin : C.inp.drop base = frame (Program.certifiedBits c) ++ rest)
    (hip : a.ip = base + 2 * z.val) :
    Hs C readColumnFlag a 3 (fun b =>
      b.env certifiedFlag = (decide (z ∈ c.certifiedColumns)).toNat ∧
      b.ip = base + 2 * (z.val + 1) ∧
      (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.out, a.ram, a.rc, a.kin, a.kout, a.kc) ∧ Cst b ∧
      Fr a b columnFlagScratch) := by
  classical
  have hz : z.val < (Program.certifiedBits c).length := by
    simpa only [Program.certifiedBits, List.length_ofFn] using z.isLt
  simpa only [Program.certifiedBits, List.getElem_ofFn] using
    readColumnFlag_run C (Program.certifiedBits c) rest base z.val hz a hc hin hip

end NearQuarticWires.StageMain.Controller
