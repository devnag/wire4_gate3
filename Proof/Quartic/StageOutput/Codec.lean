import Proof.Gates.Dispatch.Macros
import Proof.Gates.Dispatch.Run

/-!
# Binary codecs for the rounded interval

Paper: `sec:algorithm`, paper/paper.tex, and `prop:time`. The two rational outputs use signed numerators and positive
denominators, each represented by a self-delimiting binary natural number.
The programs below read and write those words with explicit step bounds.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageOutput

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Dispatch NearCubicGates.Close.Interfaces

variable {C : Ctx}

/-- Initialize the constants used by the binary arithmetic programs. -/
def constants : St VV :=
  .seq (.op (.inc v1)) (.seq (.op (.inc v2)) (.op (.inc v2)))

theorem constants_spec (hW : 2 ≤ C.Wd) :
    Hs C constants (a0 (V := VV)) 5
      (fun b => Cst b ∧ b.cp = 0 ∧ b.wq = 0 ∧ b.out = []) := by
  have h4 : 4 ≤ 2 ^ C.Wd := by
    simpa using Nat.pow_le_pow_right (n := 2) (by omega) hW
  refine Hs.mono (Hs.seq (t2 := 3) (hs_inc C v1 _ (by simp [a0]; omega)) (fun b hb => ?_)) le_rfl (fun _ h => h)
  subst hb
  refine Hs.seq (t2 := 1) (hs_inc C v2 _ (by simp [DS.set, a0, v1, v2]; omega)) (fun d hd => ?_)
  subst hd
  refine Hs.mono (hs_inc C v2 _ (by simp [DS.set, a0, v1, v2]; omega)) le_rfl ?_
  rintro e rfl
  exact ⟨⟨by simp [DS.set, a0, vZ, v1, v2],
    by simp [DS.set, a0, v1, v2], by simp [DS.set, a0, v1, v2],
    by simp [DS.set, a0, vPOS, v1, v2]⟩, rfl, rfl, rfl⟩

/-- Read one binary natural-number word and append its identical encoding. -/
def copyNat : St VV := .seq readNat emitNat

theorem copyNat_spec (a : DS VV) (hc : Cst a) (v : ℕ) (rest : List Bool)
    (hin : C.cw.drop a.cp = natWord v ++ rest)
    (hW : natBitLength v + 2 ≤ C.Wd) (hL : C.cw.length + 2 < 2 ^ C.Wd) :
    Hs C copyNat a (70 * natBitLength v + 71) (fun b =>
      b.out = a.out ++ natWord v ∧ b.cp = a.cp + (natWord v).length ∧
      b.wq = a.wq ∧ Cst b) := by
  have hv : natBitLength v + 2 < 2 ^ C.Wd := by
    have := Nat.lt_two_pow_self (n := C.Wd)
    omega
  refine Hs.mono (Hs.seq (t2 := 40 * natBitLength v + 40) (readNat_spec a hc v rest hin hW hL) (fun b hb => ?_))
    (by omega) (fun _ h => h)
  obtain ⟨hbv, _, hcp, hwq, hout, hbc, _⟩ := hb
  refine Hs.mono (emitNat_spec b hbc (by omega) (by rw [hbv]; exact hv))
    (by rw [hbv]) ?_
  rintro d ⟨hdout, hdcp, hdwq, hdc, _⟩
  exact ⟨by rw [hdout, hout, hbv], by rw [hdcp, hcp], by rw [hdwq, hwq], hdc⟩

/-- A fixed number of consecutive natural-number words. -/
def copyNats : ℕ → St VV
  | 0 => skipS
  | n + 1 => .seq copyNat (copyNats n)

def copyNatsCost (xs : List ℕ) : ℕ :=
  (xs.map fun v => 70 * natBitLength v + 72).sum + 1

theorem copyNats_spec (xs : List ℕ) (rest : List Bool)
    (hW : ∀ v ∈ xs, natBitLength v + 2 ≤ C.Wd)
    (hL : C.cw.length + 2 < 2 ^ C.Wd) :
    ∀ a : DS VV, Cst a → C.cw.drop a.cp = xs.flatMap natWord ++ rest →
    Hs C (copyNats xs.length) a (copyNatsCost xs) (fun b =>
      b.out = a.out ++ xs.flatMap natWord ∧
      b.cp = a.cp + (xs.flatMap natWord).length ∧ b.wq = a.wq ∧ Cst b) := by
  induction xs with
  | nil =>
    intro a hc _
    refine Hs.mono (skip_spec a) (by simp [copyNatsCost]) ?_
    rintro b rfl
    refine ⟨by simp, by simp, rfl, ?_⟩
    exact ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact hc.z,
      by rw [DS.set_env_ne _ _ (by decide)]; exact hc.one,
      by rw [DS.set_env_ne _ _ (by decide)]; exact hc.two,
      by rw [DS.set_env_ne _ _ (by decide)]; exact hc.pos⟩
  | cons v xs ih =>
    intro a hc hin
    have hin' : C.cw.drop a.cp = natWord v ++ (xs.flatMap natWord ++ rest) := by
      simpa only [List.flatMap_cons, List.append_assoc] using hin
    refine Hs.mono (Hs.seq (t2 := copyNatsCost xs) (copyNat_spec a hc v _ hin' (hW v (by simp)) hL)
      (fun b hb => ?_)) (by simp [copyNatsCost]; omega) (fun _ h => h)
    obtain ⟨hbout, hbcp, hbwq, hbc⟩ := hb
    have hbin : C.cw.drop b.cp = xs.flatMap natWord ++ rest := by
      rw [hbcp]
      exact drop_adv hin'
    refine Hs.mono (ih (fun u hu => hW u (by simp [hu])) b hbc hbin) le_rfl ?_
    rintro d ⟨hdout, hdcp, hdwq, hdc⟩
    refine ⟨by rw [hdout, hbout]; simp [List.append_assoc], ?_, by rw [hdwq, hbwq], hdc⟩
    rw [hdcp, hbcp]
    simp [Nat.add_assoc]

end NearQuarticWires.StageOutput
