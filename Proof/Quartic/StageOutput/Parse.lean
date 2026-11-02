import Proof.Quartic.StageOutput.Codec

/-!
# Reading the scalars of Step 5

Paper: `sec:algorithm`, paper/paper.tex. The output formulas
use the input size, dimension, sample count, filter bound, error parameter,
certified-column count, consistency bit, and the two integer totals. Their
binary encoding has thirteen natural-number fields, including signs.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageOutput

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces

variable {C : Ctx}

theorem scalar_not_readNatT {x : Fin VV} (hx : 15 ≤ x.val) : x ∉ readNatT := by
  simp only [readNatT, List.mem_cons, List.not_mem_nil, or_false, not_or]
  repeat' constructor
  all_goals intro h; subst h; norm_num [t0, t1, t2, t3, t4, vJ, vPOS] at hx

theorem scalar_not_constants {x : Fin VV} (hx : 15 ≤ x.val) :
    x ≠ vZ ∧ x ≠ v1 ∧ x ≠ v2 ∧ x ≠ vPOS := by
  repeat' constructor
  all_goals intro h; subst h; norm_num [vZ, v1, v2, vPOS] at hx

/-- Read one field into a scalar variable, retaining all other scalar variables. -/
def readScalar (x : Fin VV) : St VV := .seq readNat (.op (.copy x t3))

theorem readScalar_spec (x : Fin VV) (hx : 15 ≤ x.val) (a : DS VV) (hc : Cst a)
    (v : ℕ) (rest : List Bool) (hin : C.cw.drop a.cp = natWord v ++ rest)
    (hW : natBitLength v + 2 ≤ C.Wd) (hL : C.cw.length + 2 < 2 ^ C.Wd) :
    Hs C (readScalar x) a (30 * natBitLength v + 32) (fun b =>
      b.cp = a.cp + (natWord v).length ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧
      ∀ y : Fin VV, 15 ≤ y.val → b.env y = Function.update a.env x v y) := by
  have hxt : x ≠ t3 := by intro h; subst h; norm_num [t3] at hx
  obtain ⟨hxz, hx1, hx2, hxpos⟩ := scalar_not_constants hx
  refine Hs.mono (Hs.seq (t2 := 1) (readNat_spec a hc v rest hin hW hL) (fun b hb => ?_))
    (by omega) (fun _ h => h)
  obtain ⟨hbv, _, hbcp, hbwq, hbout, hbc, hbfr⟩ := hb
  refine Hs.mono (hs_copy C x t3 b hxt) le_rfl ?_
  rintro d rfl
  refine ⟨hbcp, hbwq, hbout, ?_, ?_⟩
  · exact ⟨by rw [DS.set_env_ne _ _ hxz.symm]; exact hbc.z,
      by rw [DS.set_env_ne _ _ hx1.symm]; exact hbc.one,
      by rw [DS.set_env_ne _ _ hx2.symm]; exact hbc.two,
      by rw [DS.set_env_ne _ _ hxpos.symm]; exact hbc.pos⟩
  · intro y hy
    by_cases hyx : y = x
    · subst hyx; simp [hbv]
    · rw [DS.set_env_ne _ _ hyx, Function.update_of_ne hyx]
      exact hbfr y (scalar_not_readNatT hy)

/-- Apply the stored-field updates in their input order. -/
def fieldEnv (fs : List (Fin VV × ℕ)) (env : Fin VV → ℕ) : Fin VV → ℕ :=
  fs.foldl (fun e xv => Function.update e xv.1 xv.2) env

theorem fieldEnv_congr (fs : List (Fin VV × ℕ)) {a b : Fin VV → ℕ}
    (h : ∀ y, 15 ≤ y.val → a y = b y) :
    ∀ y, 15 ≤ y.val → fieldEnv fs a y = fieldEnv fs b y := by
  induction fs generalizing a b with
  | nil => exact h
  | cons xv fs ih =>
    apply ih
    intro y hy
    by_cases hyx : y = xv.1
    · subst hyx; simp
    · simp only [Function.update_of_ne hyx]
      exact h y hy

/-- Read a statically specified list of scalar variables. -/
def readScalars : List (Fin VV) → St VV
  | [] => skipS
  | x :: xs => .seq (readScalar x) (readScalars xs)

def readScalarsCost (fs : List (Fin VV × ℕ)) : ℕ :=
  (fs.map fun xv => 30 * natBitLength xv.2 + 33).sum + 1

theorem readScalars_spec (fs : List (Fin VV × ℕ))
    (hx : ∀ xv ∈ fs, 15 ≤ xv.1.val)
    (hW : ∀ xv ∈ fs, natBitLength xv.2 + 2 ≤ C.Wd)
    (hL : C.cw.length + 2 < 2 ^ C.Wd) (rest : List Bool) :
    ∀ a : DS VV, Cst a → C.cw.drop a.cp = fs.flatMap (fun xv => natWord xv.2) ++ rest →
    Hs C (readScalars (fs.map Prod.fst)) a (readScalarsCost fs) (fun b =>
      b.cp = a.cp + (fs.flatMap (fun xv => natWord xv.2)).length ∧ b.wq = a.wq ∧
      b.out = a.out ∧ Cst b ∧ ∀ y, 15 ≤ y.val → b.env y = fieldEnv fs a.env y) := by
  induction fs with
  | nil =>
    intro a hc _
    refine Hs.mono (skip_spec a) (by simp [readScalarsCost]) ?_
    rintro b rfl
    refine ⟨by simp, rfl, rfl, ?_, ?_⟩
    · exact ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact hc.z,
        by rw [DS.set_env_ne _ _ (by decide)]; exact hc.one,
        by rw [DS.set_env_ne _ _ (by decide)]; exact hc.two,
        by rw [DS.set_env_ne _ _ (by decide)]; exact hc.pos⟩
    · intro y hy
      apply DS.set_env_ne
      intro h; subst h; norm_num [vJ] at hy
  | cons xv fs ih =>
    intro a hc hin
    have hin' : C.cw.drop a.cp = natWord xv.2 ++ (fs.flatMap (fun p => natWord p.2) ++ rest) := by
      simpa only [List.flatMap_cons, List.append_assoc] using hin
    refine Hs.mono (Hs.seq (t2 := readScalarsCost fs)
      (readScalar_spec xv.1 (hx xv (by simp)) a hc xv.2 _ hin' (hW xv (by simp)) hL)
      (fun b hb => ?_)) (by simp [readScalarsCost]; omega) (fun _ h => h)
    obtain ⟨hbcp, hbwq, hbout, hbc, hbenv⟩ := hb
    have hbin : C.cw.drop b.cp = fs.flatMap (fun p => natWord p.2) ++ rest := by
      rw [hbcp]
      exact drop_adv hin'
    refine Hs.mono (ih (fun p hp => hx p (by simp [hp]))
      (fun p hp => hW p (by simp [hp])) b hbc hbin) le_rfl ?_
    rintro d ⟨hdcp, hdwq, hdout, hdc, hdenv⟩
    refine ⟨by rw [hdcp, hbcp]; simp [Nat.add_assoc], by rw [hdwq, hbwq],
      by rw [hdout, hbout], hdc, ?_⟩
    intro y hy
    rw [hdenv y hy]
    exact fieldEnv_congr fs hbenv y hy

end NearQuarticWires.StageOutput
