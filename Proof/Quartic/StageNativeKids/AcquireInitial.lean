import Proof.Quartic.StageNativeKids.AcquireLayout

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKids

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Expand.PolyTab

attribute [local irreducible] framedRoleWordFunction
local notation "t" => framedRoleWordFunction.program.tapeCount

/-- `lem:print`, paper/paper.tex: the
actual cold source has only its original framed word and the paid blank
loader and role reset rulers, with no decoded metadata installed. -/
noncomputable def acquireStart (r : NativeKidsRequest) : WState (t + 15) 3 :=
  idealStart (t + 15) 3 r.word (acquireLens r)

/-- `lem:print`, paper/paper.tex: the
source loader receives precisely the actual original input plus its
own blank work tapes and paid reset ruler. -/
theorem acquireStart_source (r : NativeKidsRequest) :
    (fun j : Fin 14 => (acquireStart r).st (sourceLoadMap t j)) =
      Fin.addCases (m := 13) (n := 1) (motive := fun _ => List Bool)
        ![frame r.word, [], [], [], [], [], [], [], [], [], [], [], []]
        (fun _ : Fin 1 => List.replicate r.sourceLoadCapacity false) := by
  funext j
  refine Fin.addCases (m := 13) (n := 1) (fun k => ?_) (fun k => ?_) j
  · rw [Fin.addCases_left]
    by_cases hk : k.val = 0
    · have he : k = 0 := Fin.ext hk
      subst he
      rfl
    · have h13 : k.val ≠ 13 := by omega
      have hr : k.val ≠ 14 + t := by omega
      simp only [acquireStart, idealStart, sourceLoadMap, acquireLens,
        Fin.val_castAdd, if_neg hk, if_neg h13, if_neg hr, List.replicate_zero]
      fin_cases k <;> simp_all
  · fin_cases k
    rfl

/-- `lem:print`, paper/paper.tex: the
actual role machine's entire cold work bank is genuinely empty before
the original role packet is physically assembled. -/
theorem acquireStart_roleBlank (r : NativeKidsRequest) (j : Fin t) :
    (acquireStart r).st (sourceRoleMap t j) = [] := by
  have h0 : 14 + j.val ≠ 0 := by omega
  have h13 : 14 + j.val ≠ 13 := by omega
  have hr : 14 + j.val ≠ 14 + t := by omega
  simp only [acquireStart, idealStart, sourceRoleMap, acquireLens,
    if_neg h0, if_neg h13, if_neg hr, List.replicate_zero]

/-- `prop:time`, paper/paper.tex: the
once-only role computation has its actual budget on a blank reset
ruler separate from all retained source and ordinary work tapes. -/
theorem acquireStart_ruler (r : NativeKidsRequest) :
    (acquireStart r).st (sourceRoleRuler t) = List.replicate (framedRoleBudget r) false := by
  have h13 : 14 + t ≠ 13 := by omega
  simp [acquireStart, idealStart, sourceRoleRuler, acquireLens, h13]

/-- `lem:print`, paper/paper.tex: the
acquired-source output begins empty and does not double as a paid
reset ruler or an original source tape. -/
theorem acquireStart_output (r : NativeKidsRequest) :
    (acquireStart r).st (acquireOutput t) = [] := by
  have h0 : 15 + t ≠ 0 := by omega
  have h13 : 15 + t ≠ 13 := by omega
  have hr : 15 + t ≠ 14 + t := by omega
  simp only [acquireStart, idealStart, acquireOutput, acquireLens,
    if_neg h0, if_neg h13, if_neg hr, List.replicate_zero]

end NearQuarticWires.StageNativeKids
