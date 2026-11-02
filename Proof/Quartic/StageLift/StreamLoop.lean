import Proof.Quartic.StageLift.StreamPayload
import Proof.MachineModel.OrdinaryRadixSemantics

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires
open NearCubicGates.Close.Cells
open NearQuarticWires.StageRecovery
open NearCubicWires.RepairOrdinary.RadixSemantics (value)

/-- `lem:print`, paper/paper.tex: bounded modular
accumulation has the exact original little-endian payload semantics. -/
theorem stream_value_step (q acc power : ℕ) (bit : Bool) (bits : List Bool) :
    ((acc + if bit then power else 0) % q + ((2 * power) % q) * value bits) % q =
      (acc + power * value (bit :: bits)) % q := by
  have h := (Nat.mod_modEq (acc + if bit then power else 0) q).add
    ((Nat.mod_modEq (2 * power) q).mul_right (value bits))
  change _ % q = _ % q at h
  exact h.trans (congrArg (fun z : ℕ => z % q) (by cases bit <;> simp [value] <;> ring))

/-- `lem:print`, paper/paper.tex: reduced place
values advance exactly one binary position at every replayed payload bit. -/
theorem stream_power_step (q power n : ℕ) :
    (2 ^ n * ((2 * power) % q)) % q = (2 ^ (n + 1) * power) % q := by
  have h := (Nat.mod_modEq (2 * power) q).mul_left (2 ^ n)
  change _ % q = _ % q at h
  exact h.trans (congrArg (fun z : ℕ => z % q) (by rw [pow_succ]; ring))

/-- `lem:print`, paper/paper.tex: marker replay
reads each payload bit and its actual successor marker, stopping at the
explicit zero sentinel without a register containing raw length. -/
theorem streamPayloadLoop_spec (C : Ctx) (store : Fin MM) (bits rest : List Bool)
    (junk : List ℕ) (a : DS VV MM) (hc : Cst a) (q acc power : ℕ) (hq : 0 < q)
    (haq : a.env modulusVar = q) (hav : a.env leftVar = acc)
    (hap : a.env streamPowerVar = power) (hv : acc < q) (hp : power < q)
    (hfit : 2 * q ≤ 2 ^ C.Wd)
    (hflag : a.env t0 = (unaryFlag bits.length).toNat)
    (hin : C.inp.drop a.ip = bits ++ rest)
    (hmarkers : (a.ram store).drop (a.rc store) =
      (unaryTail bits.length).map Bool.toNat ++ junk) :
    Hs C (.loop (.eq t0 v1) (streamPayloadBody store)) a (20 * bits.length + 2) (fun b =>
      b.env leftVar = (acc + power * value bits) % q ∧
      b.env streamPowerVar = (2 ^ bits.length * power) % q ∧ b.env t0 = 0 ∧
      b.ip = a.ip + bits.length ∧ b.ram = a.ram ∧
      b.rc = Function.update a.rc store (a.rc store + bits.length) ∧
      (b.out, b.kin, b.kout, b.kc) = (a.out, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b payloadBodyScratch) := by
  induction bits generalizing a acc power with
  | nil =>
      have ht : (Cnd.eq t0 v1).eval a = false := by
        simp [Cnd.eval, hflag, unaryFlag, hc.one]
      refine ⟨a, 2, Ex.loopF (show t0 ≠ v1 by decide) ht, by simp,
        ?_, ?_, ?_, by simp, rfl, ?_, rfl, hc, Fr.refl _ _⟩
      · simpa only [value, Nat.mul_zero, Nat.add_zero, Nat.mod_eq_of_lt hv] using hav
      · simpa only [List.length_nil, pow_zero, Nat.one_mul, Nat.mod_eq_of_lt hp] using hap
      · simpa [unaryFlag] using hflag
      · funext other
        by_cases ho : other = store
        · subst other
          simp
        · simp [Function.update_of_ne ho]
  | cons bit bits ih =>
      have ht : (Cnd.eq t0 v1).eval a = true := by
        simp [Cnd.eval, hflag, unaryFlag, hc.one]
      have hmarkdrop : (a.ram store).drop (a.rc store) =
          (unaryFlag bits.length).toNat :: ((unaryTail bits.length).map Bool.toNat ++ junk) := by
        simpa only [List.length_cons, unaryTail, List.map_cons, List.cons_append] using hmarkers
      have hmark : a.rc store < (a.ram store).length := by
        have hnonempty := congrArg List.length hmarkdrop
        simp only [List.length_drop, List.length_cons] at hnonempty
        omega
      have hnext : (a.ram store).getD (a.rc store) 0 = (unaryFlag bits.length).toNat :=
        fld_of_drop hmarkdrop
      obtain ⟨b, s, he, hs, hbl, hbp, hbflag, hbi, hbr, hbrc, hbsh, hbc, hbf⟩ :=
        streamPayloadBody_spec C store a hc q acc power bit (unaryFlag bits.length)
          (bits ++ rest) hq haq hav hap hv hp hfit hin hmark hnext
      have hbq : b.env modulusVar = q := by rw [hbf _ (by decide)]; exact haq
      have hbin : C.inp.drop b.ip = bits ++ rest := by
        rw [hbi, ← List.drop_drop, hin]
        rfl
      have hbmarkers : (b.ram store).drop (b.rc store) =
          (unaryTail bits.length).map Bool.toNat ++ junk := by
        rw [hbr, hbrc, Function.update_self, ← List.drop_drop, hmarkdrop]
        rfl
      obtain ⟨d, k, hd, hk, hdl, hdp, hdz, hdi, hdr, hdrc, hdsh, hdc, hdf⟩ :=
        ih b hbc ((acc + if bit then power else 0) % q) ((2 * power) % q) hbq hbl hbp
          (Nat.mod_lt _ hq) (Nat.mod_lt _ hq) hbflag hbin hbmarkers
      refine ⟨d, s + k + 2, Ex.loopT (show t0 ≠ v1 by decide) ht he hd, by simp; omega,
        ?_, ?_, hdz, ?_, hdr.trans hbr, ?_, hdsh.trans hbsh, hdc, hbf.trans hdf⟩
      · rw [hdl, stream_value_step]
      · rw [hdp, List.length_cons, stream_power_step]
      · rw [hdi, hbi, List.length_cons]
        omega
      · rw [hdrc, hbrc, Function.update_self, Function.update_idem]
        congr 1
        simp only [List.length_cons]
        omega

end NearQuarticWires.StageLift
