import Proof.Gates.Cells.Mac
import Proof.Wire_3_5.SamplerCond

/-!
# Physical decomposition of the sampler seed

`imp:seed`, paper/paper.tex: the seed consists of eight
consecutive field words. Binary quotient and remainder operations extract
the low coefficient first, preserving the field width and all unrelated
registers. The stored coefficients can then be emitted in reverse order
for Horner evaluation in the main pass.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain
namespace SampleCells

open NearCubicGates.Close.Cells
open NearCubicWires.WireExponent3_5

def seed : Fin VV := 80
def ell : Fin VV := 81
def modulus : Fin VV := 82
def label : Fin VV := 83
def radix : Fin VV := 84
def coefficient (i : Fin 8) : Fin VV := ⟨85 + i.val, by change 85 + i.val < 128; omega⟩
def quotient : Fin VV := 93

def digitStep (x : Fin VV) (a : DS VV MM) : DS VV MM :=
  ((a.set quotient (a.env seed / a.env radix)).set x (a.env seed % a.env radix)).set seed
    (a.env seed / a.env radix)

def digitState : List (Fin VV) → DS VV MM → DS VV MM
  | [], a => a.set vJ 0
  | x :: xs, a => digitState xs (digitStep x a)

def digitProgram : List (Fin VV) → St VV MM
  | [] => .op (.zero vJ)
  | x :: xs => .seq (.op (.dm seed radix quotient x))
      (.seq (.op (.copy seed quotient)) (digitProgram xs))

theorem digitProgram_run (C : Ctx) (xs : List (Fin VV))
    (hxs : ∀ x ∈ xs, x ≠ seed ∧ x ≠ radix ∧ x ≠ quotient) (a : DS VV MM)
    (hr : 0 < a.env radix) (hfit : 2 * a.env radix ≤ 2 ^ C.Wd) :
    Hs C (digitProgram xs) a (4 * xs.length + 1) (fun b => b = digitState xs a) := by
  induction xs generalizing a with
  | nil => exact hs_zero C vJ a
  | cons x xs ih =>
    obtain ⟨hxs1, hxr, hxq⟩ := hxs x (by simp)
    have hstep : digitStep x a =
        (((a.set quotient (a.env seed / a.env radix)).set x (a.env seed % a.env radix)).set seed
          (((a.set quotient (a.env seed / a.env radix)).set x (a.env seed % a.env radix)).env quotient)) := by
      simp [digitStep, DS.set_env_ne _ _ hxq.symm]
    have hrad : (digitStep x a).env radix = a.env radix := by
      simp only [digitStep, DS.set_env_ne _ _ (by decide : radix ≠ seed),
        DS.set_env_ne _ _ hxr.symm, DS.set_env_ne _ _ (by decide : radix ≠ quotient)]
    refine Hs.mono (Hs.seq (t1 := 1) (t2 := 1 + (4 * xs.length + 1) + 1)
      (hs_dm C seed radix quotient x a (by decide) (by decide) hxs1.symm
        (by decide) hxr.symm hxq.symm hr hfit) ?_) (by simp; omega) (fun _ h => h)
    rintro b rfl
    refine Hs.seq (t1 := 1) (t2 := 4 * xs.length + 1)
      (hs_copy C seed quotient _ (by decide)) ?_
    rintro d rfl
    rw [← hstep]
    exact ih (fun y hy => hxs y (by simp [hy])) (digitStep x a)
      (by rw [hrad]; exact hr) (by rw [hrad]; exact hfit)

def coefficientRegisters : List (Fin VV) := List.ofFn coefficient

theorem coefficientRegisters_distinct :
    ∀ x ∈ coefficientRegisters, x ≠ seed ∧ x ≠ radix ∧ x ≠ quotient := by
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  have hi := i.isLt
  simp only [ne_eq, Fin.ext_iff]
  change (85 + i.val ≠ 80 ∧ 85 + i.val ≠ 84 ∧ 85 + i.val ≠ 93)
  omega

theorem splitSeed_run (C : Ctx) (a : DS VV MM)
    (hr : 0 < a.env radix) (hfit : 2 * a.env radix ≤ 2 ^ C.Wd) :
    Hs C (digitProgram coefficientRegisters) a 33
      (fun b => b = digitState coefficientRegisters a) := by
  simpa [coefficientRegisters] using
    digitProgram_run C coefficientRegisters coefficientRegisters_distinct a hr hfit

theorem digitState_env (xs : List (Fin VV)) (a : DS VV MM) (y : Fin VV)
    (hy : y ∉ xs) (hs : y ≠ seed) (hq : y ≠ quotient) (hj : y ≠ vJ) :
    (digitState xs a).env y = a.env y := by
  induction xs generalizing a with
  | nil => exact DS.set_env_ne _ _ hj
  | cons x xs ih =>
    have hyx : y ≠ x := fun h => hy (by simp [h])
    have hyt : y ∉ xs := fun h => hy (by simp [h])
    rw [digitState, ih (digitStep x a) hyt]
    simp only [digitStep, DS.set_env_ne _ _ hs, DS.set_env_ne _ _ hyx,
      DS.set_env_ne _ _ hq]

theorem digitState_nth (xs : List (Fin VV)) (hnd : xs.Nodup)
    (hxs : ∀ x ∈ xs, x ≠ seed ∧ x ≠ radix ∧ x ≠ quotient ∧ x ≠ vJ)
    (a : DS VV MM) (i : Fin xs.length) :
    (digitState xs a).env xs[i.val] = a.env seed / a.env radix ^ i.val % a.env radix := by
  induction xs generalizing a with
  | nil => exact Fin.elim0 i
  | cons x xs ih =>
    obtain ⟨hx, hn⟩ := List.nodup_cons.mp hnd
    obtain ⟨hxs1, hxr, hxq, hxj⟩ := hxs x (by simp)
    have htail := fun y (hy : y ∈ xs) => hxs y (by simp [hy])
    have hrad : (digitStep x a).env radix = a.env radix := by
      simp only [digitStep, DS.set_env_ne _ _ (by decide : radix ≠ seed),
        DS.set_env_ne _ _ hxr.symm, DS.set_env_ne _ _ (by decide : radix ≠ quotient)]
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [List.getElem_cons_zero, Fin.val_zero, pow_zero, Nat.div_one, digitState]
      rw [digitState_env xs (digitStep x a) x hx hxs1 hxq hxj]
      simp only [digitStep, DS.set_env_ne _ _ hxs1, DS.set_env_self]
    · simp only [List.getElem_cons_succ, Fin.val_succ, digitState]
      rw [ih hn htail (digitStep x a) j, hrad]
      simp only [digitStep, DS.set_env_self]
      rw [Nat.div_div_eq_div_mul, pow_succ']

theorem coefficientRegisters_nodup : coefficientRegisters.Nodup := by
  apply List.nodup_ofFn.mpr
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  change 85 + i.val = 85 + j.val at this
  omega

theorem splitSeed_coefficient (a : DS VV MM) (i : Fin 8) :
    (digitState coefficientRegisters a).env (coefficient i) =
      a.env seed / a.env radix ^ i.val % a.env radix := by
  have he : coefficientRegisters.length = 8 := by simp [coefficientRegisters]
  have hh := digitState_nth coefficientRegisters coefficientRegisters_nodup
    (fun x hx => by
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
      simp only [ne_eq, Fin.ext_iff]
      change (85 + j.val ≠ 80 ∧ 85 + j.val ≠ 84 ∧ 85 + j.val ≠ 93 ∧ 85 + j.val ≠ 3)
      omega) a ⟨i.val, by rw [he]; exact i.isLt⟩
  simpa only [coefficientRegisters, List.getElem_ofFn] using hh

theorem splitSeed_sampler (a : DS VV MM) (n s : ℕ) (hn : a.env radix = 2 ^ n)
    (hs : a.env seed = s) (i : Fin 8) :
    (digitState coefficientRegisters a).env (coefficient i) = Sampler.seedCoeff n s i := by
  rw [splitSeed_coefficient, hn, hs]
  simp only [Sampler.seedCoeff, Nat.shiftRight_eq_div_pow, ← pow_mul, Nat.mul_comm]

end SampleCells
end NearQuarticWires.StageMain
