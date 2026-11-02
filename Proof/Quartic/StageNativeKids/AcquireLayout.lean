import Proof.Quartic.StageNativeKids.SourceRole
import Proof.Quartic.StageNativeKids.AcquireFormat

set_option autoImplicit false

namespace NearQuarticWires.StageNativeKids

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms

attribute [local irreducible] framedRoleWordFunction

/-- `lem:print`, paper/paper.tex: the
acquired source is printed on a fresh tape outside both the original
loader bank and the actual ordinary role-callee bank. -/
def acquireOutput (t : ℕ) : Fin (t + 16) := ⟨15 + t, by omega⟩

/-- `lem:print`, paper/paper.tex: the
actual source formatter reads the retained original record and the
real role reply, writing their exact next eleven-field source. -/
def acquireSources (p : Program) : Fin 3 ↪ Fin (p.tapeCount + 16) where
  toFun := ![sourceLoadMap p.tapeCount 1, sourceRoleMap p.tapeCount p.outputTape,
    acquireOutput p.tapeCount]
  inj' := by
    intro i j h
    have hp := p.outputTape.isLt
    fin_cases i <;> fin_cases j <;>
      first | rfl | skip
    · have hv : 1 = 14 + p.outputTape.val := congrArg (fun k => k.val) h
      omega
    · have hv : 1 = 15 + p.tapeCount := congrArg (fun k => k.val) h
      omega
    · have hv : 14 + p.outputTape.val = 1 := congrArg (fun k => k.val) h
      omega
    · have hv : 14 + p.outputTape.val = 15 + p.tapeCount := congrArg (fun k => k.val) h
      omega
    · have hv : 15 + p.tapeCount = 1 := congrArg (fun k => k.val) h
      omega
    · have hv : 15 + p.tapeCount = 14 + p.outputTape.val := congrArg (fun k => k.val) h
      omega

/-- `prop:time`, paper/paper.tex: the
cold source uses only its actual loader workspace and once-only role
reset ruler; the final acquired-source tape starts genuinely empty. -/
noncomputable def acquireLens (r : NativeKidsRequest)
    (i : Fin (framedRoleWordFunction.program.tapeCount + 16)) : ℕ :=
  if i.val = 13 then r.sourceLoadCapacity
  else if i.val = 14 + framedRoleWordFunction.program.tapeCount then framedRoleBudget r else 0

/-- `prop:time`, paper/paper.tex: source
copying registers have a capacity linear in the actual finite original
source, binary role packet and exact role reply, independent of the
numeric values of the canonical radix and walk ordinal. -/
def acquireCapacity (r : NativeKidsRequest) : ℕ :=
  4 * (r.word.length + (r.toRowContext.rolePacket r.atom).word.length + r.rolePayload.length + 1) + 100

/-- `lem:print`, paper/paper.tex: a cold
source computation runs actual acquisition and then the physical
acquired-record formatter without any decoded role or selected-row input. -/
noncomputable def acquireProgram :
    WMX (framedRoleWordFunction.program.tapeCount + 15) 3 :=
  .seq sourceRoleProgram (.wm (acquireFormatProgram
    (acquireSources framedRoleWordFunction.program) 0 1))

/-- `prop:time`, paper/paper.tex: the
complete first-stage clock includes source acquisition, the real role
callee and every output record marker and delimiter. -/
noncomputable def acquireClock (r : NativeKidsRequest) : ℕ :=
  sourceRoleClock r + acquireFormatCost r + 1

end NearQuarticWires.StageNativeKids
