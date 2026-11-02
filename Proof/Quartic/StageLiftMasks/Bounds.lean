import Proof.Quartic.StageLiftMasks.State
import Proof.Quartic.StageCert.MomentBitBounds
import Proof.Quartic.StageLift.SourceArithmetic

/-!
# Binary bounds for actual mask requests

`lem:maskpoly`, `lem:print` and `prop:time`, paper/paper.tex: selected parameters
bound the real atom, pattern and signed Newton words. Tuple counts
remain exponential in the selected mask degree.
-/

set_option autoImplicit false

namespace NearQuarticWires.StageLiftMasks
open NearCubicWires NearCubicGates.Close.Cells
open StageLift StageCert.Tokens

variable {B1 B2 : ℕ}

theorem source_Xmax_le (r : Greedy.PrintRequest B1 B2) :
    r.child.selected.1.Xmax≤ sourceEnvelope r := by
  have hs:=Cells.prepare_spec _ r.child.selected.1 r.child.selected.2
  have ha:=(Program.dispatch_admitted r.child.dispatched).1
  have hb : 1≤r.child.call.radius*(r.child.call.n:ℚ)^B1 := ha.2.2.2.2.2.2.2.2.2.1
  have hx : r.child.selected.1.Xmax≤Cells.ParameterArithmetic.preparationEnvelope B1 r.child.call.n :=
    (hs.scalar_preparation_bounds B1 hb).Xmax
  exact hx.trans (by unfold sourceEnvelope; omega)

theorem prepared_length_le (r : Greedy.PrintRequest B1 B2) :
    (preparedWordOf r).length≤ sourceEnvelope r := by unfold sourceEnvelope; omega

theorem source_N_bits (r : Greedy.PrintRequest B1 B2) :
    natBitLength r.child.selected.1.N≤ sourceEnvelope r+1 := by
  have hs:=Cells.prepare_spec _ r.child.selected.1 r.child.selected.2
  rw [hs.N_eq]
  unfold natBitLength
  rw [Nat.log_pow (by decide : 1<(2:ℕ))]
  have hk:=(sourceEnvelope_bounds r).partition
  have hd:=Nat.div_le_self r.child.selected.1.k 2
  omega

theorem structural_left_bits (r : Greedy.PrintRequest B1 B2)
    (index : Fin (r.child.cellCall.seed.N^8)) (edge : Fin 8) :
    natBitLength (printMaskStructuralRequest r index edge).left.val≤ sourceEnvelope r+1 :=
  (codec_nbl_mono ((printMaskStructuralRequest r index edge).left.isLt.le.trans
    (request_N r).le)).trans (source_N_bits r)

theorem structural_right_bits (r : Greedy.PrintRequest B1 B2)
    (index : Fin (r.child.cellCall.seed.N^8)) (edge : Fin 8) :
    natBitLength (printMaskStructuralRequest r index edge).right.val≤ sourceEnvelope r+1 :=
  (codec_nbl_mono ((printMaskStructuralRequest r index edge).right.isLt.le.trans
    (request_N r).le)).trans (source_N_bits r)

theorem atom_pool_power_bound (E : ℕ) (hE : 2≤E) : 17*E<2^(2*(E+1)) := by
  obtain ⟨d,rfl⟩:=Nat.exists_eq_add_of_le hE
  clear hE
  induction d with
  | zero => norm_num
  | succ d ih =>
    rw [show 2*(2+(d+1)+1)=2*(2+d+1)+2 by omega,pow_add]
    norm_num
    nlinarith

theorem source_atom_bits (r : Greedy.PrintRequest B1 B2) (g : ℕ)
    (hg : g<(Builder.allGates r.child.call).length) (edge : Fin 8) (corner : Fin 4) :
    natBitLength (cornerRoleCode edge corner*(Builder.allGates r.child.call).length+g)≤
      2*(sourceEnvelope r+1) := by
  have hi := (Cells.atomIndex (Cells.cornerRole (by decide : 0<4) edge corner)
    (⟨g,hg⟩ : Fin (Builder.allGates r.child.call).length)).isLt
  rw [atomIndex_eq_code] at hi
  have he:=(sourceEnvelope_bounds r).positive
  have hG:=(sourceEnvelope_bounds r).occurrences
  apply nbl_le_of_lt _ (by omega)
  exact hi.trans ((Nat.mul_le_mul_left 17 hG).trans_lt (atom_pool_power_bound _ he))

theorem source_newton_bits (r : Greedy.PrintRequest B1 B2) (d : ℕ)
    (hd : d≤r.child.selected.1.Xmax) :
    natBitLength (Mask.newtonCoeff r.child.selected.1.tau d).natAbs≤4*(sourceEnvelope r+1) := by
  have h:=Mask.newtonCoeff_abs_le r.child.selected.1.tau d
  rw [←Int.natCast_natAbs] at h
  have hn : (Mask.newtonCoeff r.child.selected.1.tau d).natAbs≤2^d := by exact_mod_cast h
  have hb:=codec_nbl_mono hn
  have hp : natBitLength (2^d)=d+1 := by
    unfold natBitLength
    rw [Nat.log_pow (by decide : 1<(2:ℕ))]
  rw [hp] at hb
  have hx:=source_Xmax_le r
  omega

end NearQuarticWires.StageLiftMasks
