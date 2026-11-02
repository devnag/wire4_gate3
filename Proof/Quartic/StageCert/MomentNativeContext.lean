import Proof.Quartic.StageCert.MomentSumMeaning
import Proof.Quartic.StageNativeMeaning.Formula
import Proof.Quartic.StageNativeMeaning.Atoms

set_option autoImplicit false

namespace NearQuarticWires.StageCert.Tokens
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.ThresholdCompiler
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Tabulator

/-- `sec:params` and `lem:print`, paper/paper.tex: actual dispatch supplies the original normalized
gate-word bounds at every repeated occurrence label. -/
theorem MomentRequest.original_gate_bits {B1 B2 : ℕ} (r : MomentRequest B1 B2)
    (i : Fin (Builder.allGates r.call).length) :
    GateBits (Call.B0 r.call.n) (StagePrint.callAtoms r.call i) := by
  have ha := (Program.dispatch_admitted r.dispatched).1
  have hi : StagePrint.callAtoms r.call i∈r.call.first.gates++r.call.second.gates := by
    exact List.getElem_mem i.isLt
  rcases List.mem_append.mp hi with hi | hi
  · exact ha.2.1.2.2.2 _ hi
  · exact ha.2.2.1.2.2.2 _ hi

/-- `eq:testX`–`eq:testPhi` and `lem:print`, paper/paper.tex: population's N² ordinal embeds
into the same eight-digit role decoder with higher digits zero. -/
theorem MomentRequest.index_lt_walk_count {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    r.index.val<r.rules.seedParameters.N^8 := by
  rw [r.rules.seed_N]
  apply r.index.isLt.trans_le
  cases r.test with
  | population =>
    exact Nat.pow_le_pow_right
      ((Cells.ParameterRules.N_ge_two r.rules).trans' (by decide)) (by decide : 2≤8)
  | digit _ _ _ => exact le_rfl
  | finalError _ _ => exact le_rfl

/-- `lem:print`, paper/paper.tex: the actual
source term determines its native role context entirely from the
same original call, parameters, witness and low-first term ordinal. -/
def MomentRequest.nativeContext {B1 B2 : ℕ} (r : MomentRequest B1 B2) : StageTuple.RowContext where
  header := ⟨r.call,r.selected.1,r.rules,r.witness⟩
  walkCode := ⟨r.index.val,r.index_lt_walk_count⟩
  gate_bits := r.original_gate_bits

/-- `sec:walks` and `lem:print`, paper/paper.tex: the actual source and original-child role
formatter use the same eight low-first walk coordinates. -/
theorem MomentRequest.native_walk_eq {B1 B2 : ℕ} (r : MomentRequest B1 B2) :
    StagePrint.indexedWalk r.rules.seedParameters.N r.nativeContext.walkCode=r.walk := by
  funext l
  apply Fin.ext
  change r.index.val/r.rules.seedParameters.N^l.val%r.rules.seedParameters.N=
    r.index.val/r.selected.1.N^l.val%r.selected.1.N
  rw [r.rules.seed_N]

/-- `imp:partition`, `imp:pullback` and `lem:print`, paper/paper.tex: the actual native
atom vector on the valid rectangle is precisely the original source
term's atom vector at its canonical original column. -/
theorem MomentRequest.native_atoms_eq {B1 B2 : ℕ} (r : MomentRequest B1 B2)
    (row : Fin (2^PrimT.C4Geo.dR r.rules.starParams))
    (column : Fin (2^PrimT.C4Geo.dRow r.rules.starParams)) :
    NearCubicGates.Close.Tabulator.boolPoint
      (StagePrint.NativeMeaning.actualAtom r.nativeContext row.val column.val)=
        r.termAtoms (StagePrint.centerIndex r.call r.rules column row) := by
  have h := congrArg NearCubicGates.Close.Tabulator.boolPoint
    (StageNativeMeaning.actualAtom_centerIndex r.nativeContext row column)
  exact h.trans (congrArg
    (fun walk : Cycle.Walk r.rules.seedParameters.N 4=>
      NearCubicGates.Close.Tabulator.boolPoint
        (Cells.walkAtomPoint r.rules.starParams (by decide : 0<4)
          (StagePrint.callPatterns r.call r.rules walk) (StagePrint.callAtoms r.call)
          (Builder.center r.call r.rules r.witness
            (StagePrint.centerIndex r.call r.rules column row)))) r.native_walk_eq)

end NearQuarticWires.StageCert.Tokens
