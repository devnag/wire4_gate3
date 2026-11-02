import Proof.Quartic.StageNativeKids.SourceLoad
import Proof.Quartic.StageNativeKids.RoleReady
import Proof.Gates.CounterMachine.TabCallDock

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKids

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CounterMachine

/-- `lem:print`, paper/paper.tex: the actual
eleven-field source loader occupies its own fourteen physical tapes. -/
def sourceLoadMap (t : ℕ) (j : Fin 14) : Fin (t + 16) := ⟨j.val, by omega⟩

/-- `lem:print`, paper/paper.tex: every
ordinary role-callee tape is disjoint from the retained source bank. -/
def sourceRoleMap (t : ℕ) (j : Fin t) : Fin (t + 16) := ⟨14 + j.val, by omega⟩

/-- `lem:print`, paper/paper.tex: the
once-only role computation has its own blank ordinary reset ruler. -/
def sourceRoleRuler (t : ℕ) : Fin (t + 16) := ⟨14 + t, by omega⟩

/-- `lem:print`, paper/paper.tex: source
assembly reads the actual affine prefix, context and atom tapes, and
writes only the input tape of the disjoint ordinary role machine. -/
def sourceRoleSources (t : ℕ) : Fin 4 ↪ Fin (t + 16) where
  toFun := ![⟨3, by omega⟩, ⟨4, by omega⟩, ⟨5, by omega⟩, ⟨14, by omega⟩]
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

/-- `lem:print`, paper/paper.tex: the
original source loader has pairwise distinct physical tape addresses. -/
theorem sourceLoadMap_injective (t : ℕ) : Function.Injective (sourceLoadMap t) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun k : Fin (t + 16) => k.val) h

/-- `lem:print`, paper/paper.tex: the
actual role callee is docked injectively on its separate tape bank. -/
theorem sourceRoleMap_injective (t : ℕ) : Function.Injective (sourceRoleMap t) := by
  intro i j h
  apply Fin.ext
  have hh := congrArg Fin.val h
  change 14 + i.val = 14 + j.val at hh
  omega

/-- `lem:print`, paper/paper.tex: no
retained original source tape is used as a role-machine work tape. -/
theorem sourceRoleMap_off (t : ℕ) (i : Fin t) (j : Fin 14) :
    sourceRoleMap t i ≠ sourceLoadMap t j := by
  intro h
  have hh := congrArg Fin.val h
  change 14 + i.val = j.val at hh
  omega

/-- `lem:print`, paper/paper.tex: the
actual reset ruler is separate from every ordinary role-machine tape. -/
theorem sourceRoleMap_ruler (t : ℕ) (i : Fin t) :
    sourceRoleMap t i ≠ sourceRoleRuler t := by
  intro h
  have hh := congrArg Fin.val h
  change 14 + i.val = 14 + t at hh
  omega

/-- `lem:print`, paper/paper.tex: the
fixed fourth assembler tape is exactly the genuine callee input tape. -/
theorem sourceRoleSources_input (p : Program) :
    sourceRoleSources p.tapeCount 3 = sourceRoleMap p.tapeCount (tape0 p) := rfl

end NearQuarticWires.StageNativeKids
