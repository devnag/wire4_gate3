import Proof.Gates.Cells.Loop

set_option autoImplicit false

namespace NearQuarticWires.StagePullback.Digits

open NearCubicGates.Close.Cells

/-- `imp:partition`, paper/paper.tex: the encoded
translation or error and its block radix. -/
def number : Fin VV := 80
def radix : Fin VV := 81
def block : Fin VV := 82
def quotient : Fin VV := 83
def current : Fin VV := 84
def counter : Fin VV := 85
def digit : Fin VV := 86

/-- `imp:partition` and `lem:print`, paper/paper.tex: successive radix divisions retain the next block. -/
def step : St VV MM := .seq (.op (.dm current radix quotient digit))
  (.op (.copy current quotient))

/-- `imp:partition` and `lem:print`, paper/paper.tex: extract a block digit without constructing a large
power or an exponential table of star patterns. -/
def program : St VV MM := .seq (.op (.copy current number))
  (.seq (forS counter block step) (.op (.dm current radix quotient digit)))

def scratch : List (Fin VV) := [current, quotient, digit, counter]

/-- `imp:partition` and `prop:time`, paper/paper.tex: the physical block-digit computation takes linear
many bounded-width divisions and preserves every source component. -/
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

end NearQuarticWires.StagePullback.Digits
