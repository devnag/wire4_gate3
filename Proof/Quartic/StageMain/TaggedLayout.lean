import Proof.Quartic.StageMain.TaggedBranch

/-!
# Disjoint banks for the main-pass call selector

Step 4 of `sec:algorithm`, paper/paper.tex: the two
fixed subroutines have disjoint physical tape banks, with a common
input, answer port and blank reset ruler outside both banks.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageMain.Tagged

variable (l r : ℕ)

def leftBank (j : Fin l) : Fin (l + r + 3) := ⟨j.val + 2, by omega⟩
def rightBank (j : Fin r) : Fin (l + r + 3) := ⟨l + j.val + 2, by omega⟩
def sharedRuler : Fin (l + r + 3) := ⟨l + r + 2, by omega⟩

theorem leftBank_injective : Function.Injective (leftBank l r) := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  dsimp [leftBank] at this
  omega

theorem rightBank_injective : Function.Injective (rightBank l r) := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  dsimp [rightBank] at this
  omega

theorem leftBank_off (j : Fin l) : leftBank l r j ≠ 0 ∧ leftBank l r j ≠ 1 ∧
    leftBank l r j ≠ sharedRuler l r := by
  constructor
  · intro h; have := congrArg Fin.val h; simp only [leftBank, Fin.val_zero] at this; omega
  constructor
  · intro h; have := congrArg Fin.val h
    change j.val + 2 = 1 % (l + r + 3) at this
    rw [Nat.mod_eq_of_lt (by omega)] at this
    omega
  · intro h; have := congrArg Fin.val h; dsimp [leftBank, sharedRuler] at this; omega

theorem rightBank_off (j : Fin r) : rightBank l r j ≠ 0 ∧ rightBank l r j ≠ 1 ∧
    rightBank l r j ≠ sharedRuler l r := by
  constructor
  · intro h; have := congrArg Fin.val h; simp only [rightBank, Fin.val_zero] at this; omega
  constructor
  · intro h; have := congrArg Fin.val h
    change l + j.val + 2 = 1 % (l + r + 3) at this
    rw [Nat.mod_eq_of_lt (by omega)] at this
    omega
  · intro h; have := congrArg Fin.val h; dsimp [rightBank, sharedRuler] at this; omega

theorem banks_disjoint (i : Fin l) (j : Fin r) : leftBank l r i ≠ rightBank l r j := by
  intro h
  have := congrArg Fin.val h
  dsimp [leftBank, rightBank] at this
  omega

theorem sharedRuler_off : sharedRuler l r ≠ 0 ∧ sharedRuler l r ≠ 1 := by
  constructor
  · intro h; have := congrArg Fin.val h; simp only [sharedRuler, Fin.val_zero] at this; omega
  · intro h; have := congrArg Fin.val h
    change l + r + 2 = 1 % (l + r + 3) at this
    rw [Nat.mod_eq_of_lt (by omega)] at this
    omega

end NearQuarticWires.StageMain.Tagged
