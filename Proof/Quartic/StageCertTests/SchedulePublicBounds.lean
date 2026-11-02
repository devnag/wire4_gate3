import Proof.Quartic.StageCertTests.ScheduleBounds
import Proof.Quartic.Cells.ParametersCallEncoding
import Proof.Quartic.StageMain.CallSize

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageCertTests

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

/-- `sec:params`, paper/paper.tex:
all scalar, list-count, sorted-prime and factor natural fields
occur in their exact public serialization order. -/
def scheduleParameterFields (p : Cells.Parameters) : List ℕ :=
  StageLift.parameterHeadFields p ++ p.primes.sort (· ≤ ·) ++ StageLift.parameterTailFields p ++ p.factors

/-- `sec:params`, paper/paper.tex:
the exact public parameter serialization pays every natural field. -/
theorem scheduleParameterFields_word (p : Cells.Parameters) :
    (scheduleParameterFields p).flatMap natWord = Program.parametersWord p := by
  rw [StageLift.parametersWord_field_layout]
  simp only [scheduleParameterFields,List.flatMap_append]

/-- `prop:time`, paper/paper.tex:
the binary scalar mass never exceeds its actual self-delimiting word length. -/
theorem bitMass_le_word_length (values : List ℕ) :
    (values.map natBitLength).sum ≤ (values.flatMap natWord).length := by
  induction values with
  | nil => simp
  | cons value values ih =>
      simp only [List.map_cons,List.sum_cons,List.flatMap_cons,List.length_append,natWord_length]
      omega

/-- `sec:params` and `prop:time`, paper/paper.tex: the unpowered scheduling header is polynomial in
the actual public parameter word and its selected scalar envelope. -/
theorem scheduleHint_le_word (p : Cells.Parameters) (V : ℕ)
    (hfields : ∀ field : ScheduleField, field.value p ≤ V) :
    scheduleHint p ≤ 1000*((Program.parametersWord p).length+V+1)^2 := by
  let L := (Program.parametersWord p).length
  let mass := ((scheduleHeaderScalars p).map natBitLength).sum
  let E := L+V+1
  have hE : 1 ≤ E := by dsimp [E];omega
  have hmain := bitMass_le_word_length (scheduleParameterFields p)
  rw [scheduleParameterFields_word] at hmain
  have hk : p.k ≤ V := hfields .k
  have hJ : p.J ≤ V := hfields .chainLength
  have hX : p.Xmax ≤ V := hfields .populationBase
  have hD : p.hE ≤ V := hfields .digitBase
  have hP : p.Lambda ≤ V := hfields .errorBase
  have hkb := NearCubicGates.Close.WorkerArith.WorkerBounds.nbl_le_self (8*p.k)
  have hJb := NearCubicGates.Close.WorkerArith.WorkerBounds.nbl_le_self p.J
  have hXb := NearCubicGates.Close.WorkerArith.WorkerBounds.nbl_le_self (p.Xmax+1)
  have hDb := NearCubicGates.Close.WorkerArith.WorkerBounds.nbl_le_self p.hE
  have hPb := NearCubicGates.Close.WorkerArith.WorkerBounds.nbl_le_self p.Lambda
  have hm : mass ≤ L+12*V+6 := by
    change ((scheduleParameterFields p ++ [8*p.k,p.J,p.Xmax+1,p.hE,p.Lambda]).map natBitLength).sum ≤ _
    simp only [List.map_append,List.sum_append,List.map_cons,List.sum_cons,List.map_nil,List.sum_nil]
    dsimp only [L] at *
    omega
  have hmE : mass ≤ 12*E := by dsimp [E];omega
  have hkE : p.k ≤ E := by dsimp [E];omega
  have hprod := Nat.mul_le_mul (Nat.mul_le_mul_left 8 hkE) (Nat.add_le_add_right hmE 1)
  change 10+mass+8*p.k*(mass+1) ≤ 1000*E^2
  nlinarith

/-- `prop:time`, paper/paper.tex:
the scheduler's width coefficient depends only on the public
normalization precision exponent. -/
def scheduleWidthCoefficient (B1 : ℕ) : ℕ :=
  1000*(101*Cells.ParameterArithmetic.preparationCoefficient B1+401)^2

/-- `sec:params` and `prop:time`, paper/paper.tex: on an actual dispatched call, the exact small
scheduling header is polynomially bounded in the original call word. -/
theorem dispatched_scheduleHint_word {B1 B2 : ℕ} {c : Call} {p : Program.Selected c}
    (hd : Program.dispatch B1 B2 c = some p) :
    scheduleHint p.1 ≤ scheduleWidthCoefficient B1*((callWord c).length+1)^(2*(B1+12)) := by
  let L := (callWord c).length
  let V := Cells.ParameterArithmetic.preparationEnvelope B1 c.n
  let Y := (L+1)^(B1+12)
  let C := Cells.ParameterArithmetic.preparationCoefficient B1
  have hs := Cells.prepare_spec _ p.1 p.2
  have hadm := (Program.dispatch_admitted hd).1
  have hb : 1 ≤ c.radius*(c.n:ℚ)^B1 := hadm.2.2.2.2.2.2.2.2.2.1
  have hscalar := hs.scalar_preparation_bounds B1 hb
  have hfields : ∀ field : ScheduleField, field.value p.1 ≤ V := by
    intro field
    cases field
    · exact hscalar.k
    · exact hscalar.Xmax
    · exact hscalar.hE
    · exact hscalar.J
    · exact hscalar.Lambda
  have hh := scheduleHint_le_word p.1 V hfields
  have hS : (Program.parametersWord p.1).length ≤ 100*(C+4)*Y := Cells.dispatched_parametersWord_length hd
  have hn : c.n ≤ L := Cells.dispatched_n_le_callWord hd
  have hV : V ≤ C*Y := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) _)
  have hY : 1 ≤ Y := Nat.one_le_pow _ _ (by dsimp [L];omega)
  have hbase : (Program.parametersWord p.1).length+V+1 ≤ (101*C+401)*Y := by nlinarith
  calc
    scheduleHint p.1 ≤ 1000*((Program.parametersWord p.1).length+V+1)^2 := hh
    _ ≤ 1000*((101*C+401)*Y)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbase 2)
    _ = scheduleWidthCoefficient B1*((callWord c).length+1)^(2*(B1+12)) := by
      have halg (A X D : ℕ) : 1000*(A*X^D)^2 = (1000*A^2)*X^(2*D) := by
        rw [mul_pow,←pow_mul,Nat.mul_comm D 2]
        ring
      exact halg (101*C+401) (L+1) (B1+12)

/-- `prop:time`, paper/paper.tex:
the exact actual-call header can be allocated from its arity alone,
with no following witness, bitmap or native table in the width. -/
theorem dispatched_scheduleHint_arity {B1 B2 : ℕ} {c : Call} {p : Program.Selected c}
    (hd : Program.dispatch B1 B2 c = some p) :
    scheduleHint p.1 ≤ scheduleWidthCoefficient B1*1002^(2*(B1+12))*
      (c.n+1)^((B2+8)*(2*(B1+12))) := by
  have hc := StageMain.CallSize.dispatched_callWord_polynomial hd
  have hy : 1 ≤ (c.n+1)^(B2+8) := Nat.one_le_pow _ _ (by omega)
  have hl : (callWord c).length+1 ≤ 1002*(c.n+1)^(B2+8) := by omega
  calc
    scheduleHint p.1 ≤ scheduleWidthCoefficient B1*((callWord c).length+1)^(2*(B1+12)) :=
      dispatched_scheduleHint_word hd
    _ ≤ scheduleWidthCoefficient B1*(1002*(c.n+1)^(B2+8))^(2*(B1+12)) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hl _)
    _ = _ := by rw [mul_pow,←pow_mul];ring

end NearQuarticWires.StageCertTests
