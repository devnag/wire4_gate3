import Proof.Gates.Cells.Loop

set_option autoImplicit false

namespace NearQuarticWires.StagePrint.Header.WalkDigits

open NearCubicGates.Close.Cells

/-- `sec:walks` and `lem:print`, paper/paper.tex: the actual walk-address counter is decoded in the canonical low-first radix. -/
def number : Fin VV := 54
def radix : Fin VV := 98
def block : Fin VV := 99
def quotient : Fin VV := 101
def current : Fin VV := 100
def counter : Fin VV := 103
def digit : Fin VV := 102

/-- `sec:walks` and `lem:print`, paper/paper.tex: one physical division removes a walk coordinate. -/
def step : St VV MM := .seq (.op (.dm current radix quotient digit))
  (.op (.copy current quotient))

/-- `sec:walks` and `lem:print`, paper/paper.tex: the requested walk coordinate is extracted by actual bounded-width divisions. -/
def program : St VV MM := .seq (.op (.copy current number))
  (.seq (forS counter block step) (.op (.dm current radix quotient digit)))

def scratch : List (Fin VV) := [current, quotient, digit, counter]

/-- `sec:walks`, `lem:print` and `prop:time`, paper/paper.tex: decoding one actual walk coordinate preserves all source data and costs linearly many divisions in its slot, which is at most seven. -/
theorem program_run (C : Ctx) (a : DS VV MM)
    (hr : 0 < a.env radix) (hrfit : 2 * a.env radix ≤ 2 ^ C.Wd)
    (hbfit : a.env block < 2 ^ C.Wd) :
    Hs C program a (7 * a.env block + 8) (fun b =>
      b.env digit = a.env number / a.env radix ^ a.env block % a.env radix ∧
      b.sh = a.sh ∧ Fr a b scratch) := by
  let N := a.env block
  let B := a.env radix
  let X := a.env number
  let I : ℕ → DS VV MM → Prop := fun k e =>
    e.env current = X / B ^ k ∧ e.env radix = B ∧
      e.sh = a.sh ∧ Fr a e scratch
  refine Hs.mono (Hs.seq (t1 := 1) (t2 := (N * (3 + 4) + 4) + 1 + 1)
    (hs_copy C current number a (by decide)) ?_) (by dsimp [N]; omega) (fun _ h => h)
  rintro b rfl
  have hloop := forS_spec' (C := C) counter block (by decide) step
    (a.set current X) N hbfit I 3
    (fun k e v ⟨hv, hrad, hs, hf⟩ => ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact hv,
      by rw [DS.set_env_ne _ _ (by decide)]; exact hrad, hs,
      hf.trans (Fr.set e v (by simp [scratch]))⟩)
    ⟨by simp [X], by simp [B, DS.set_env_ne _ _ (by decide : radix ≠ current)],
      rfl, Fr.set a X (by simp [scratch])⟩
    (by rw [DS.set_env_ne _ _ (by decide)]) ?_
  · refine Hs.mono (Hs.seq (t1 := N * (3 + 4) + 4) (t2 := 1) hloop ?_)
      (by omega) (fun _ h => h)
    rintro e ⟨⟨hv, hrad, hs, hf⟩, _, heblock⟩
    refine Hs.mono (hs_dm C current radix quotient digit e (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by rw [hrad]; exact hr) (by rw [hrad]; exact hrfit)) le_rfl ?_
    rintro f rfl
    refine ⟨by rw [DS.set_env_self, hv, hrad], hs, ?_⟩
    exact hf.trans ((Fr.set e _ (by simp [scratch])).trans (Fr.set _ _ (by simp [scratch])))
  · intro k hk e ⟨hv, hrad, hs, hf⟩ hecount heblock
    unfold step
    refine Hs.seq (t1 := 1) (t2 := 1)
      (hs_dm C current radix quotient digit e (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by rw [hrad]; exact hr) (by rw [hrad]; exact hrfit)) ?_
    rintro d rfl
    refine Hs.mono (hs_copy C current quotient _ (by decide)) le_rfl ?_
    rintro f rfl
    refine ⟨⟨?_, ?_, hs, ?_⟩, ?_, ?_⟩
    · rw [DS.set_env_self, DS.set_env_ne _ _ (by decide), DS.set_env_self, hv, hrad]
      rw [Nat.div_div_eq_div_mul, pow_succ]
    · simp only [DS.set_env_ne _ _ (by decide : radix ≠ current),
        DS.set_env_ne _ _ (by decide : radix ≠ digit),
        DS.set_env_ne _ _ (by decide : radix ≠ quotient), hrad]
    · exact hf.trans ((Fr.set e _ (by simp [scratch])).trans
        ((Fr.set _ _ (by simp [scratch])).trans (Fr.set _ _ (by simp [scratch]))))
    · simp only [DS.set_env_ne _ _ (by decide : counter ≠ current),
        DS.set_env_ne _ _ (by decide : counter ≠ digit),
        DS.set_env_ne _ _ (by decide : counter ≠ quotient), hecount]
    · simp only [DS.set_env_ne _ _ (by decide : block ≠ current),
        DS.set_env_ne _ _ (by decide : block ≠ digit),
        DS.set_env_ne _ _ (by decide : block ≠ quotient), heblock]

end NearQuarticWires.StagePrint.Header.WalkDigits
