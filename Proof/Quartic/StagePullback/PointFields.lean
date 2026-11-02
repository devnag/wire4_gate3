import Proof.Quartic.StagePullback.PointRequest
import Proof.Quartic.StageGamma.ReadFields
import Proof.Gates.CounterMachine.CellTablesBody1

set_option autoImplicit false

namespace NearQuarticWires.StagePullback

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicGates.Close.Cells
open NearCubicGates.Close.CounterMachine.CellTablesProg

/-- `imp:partition` and Step 4 of `sec:algorithm`, paper/paper.tex: nine scalar fields specify the requested
canonical center and its two sampled error patterns. -/
def PointRequest.fields (q : PointRequest) : List ℕ :=
  [q.parameters.n, q.parameters.r, q.parameters.b, q.parameters.s,
    translationNumber q.parameters q.translation, q.row.val, q.column.val,
    q.left.val, q.right.val]

/-- `imp:partition`, paper/paper.tex: the scalar
header has constant field count. -/
theorem PointRequest.fields_length (q : PointRequest) : q.fields.length = 9 := rfl

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
the scalar header followed by two corner bits is the exact request word. -/
theorem PointRequest.fields_word (q : PointRequest) :
    q.fields.flatMap natWord ++ [q.useLeft, q.useRight] = q.word := by
  simp [PointRequest.fields, PointRequest.word, List.append_assoc]

/-- `imp:partition`, paper/paper.tex: all scalar
codes, including the translation, fit in the original input dimension. -/
theorem PointRequest.fields_lt (q : PointRequest) (v : ℕ) (hv : v ∈ q.fields) :
    v < 2 ^ (q.parameters.n + 1) := by
  let P := q.parameters
  have hr : P.r ≤ P.n := by have := P.four_r_le_n; omega
  have hb : P.b ≤ P.n :=
    (Nat.le_mul_of_pos_left _ P.r_pos).trans P.r_mul_b_le
  have hs : P.s ≤ P.n := P.s_le_b.trans hb
  have hk : P.s * P.r ≤ P.n := by
    rw [Nat.mul_comm]
    exact (Nat.mul_le_mul_left P.r P.s_le_b).trans P.r_mul_b_le
  have hd : PrimT.C4Geo.dRow P ≤ P.n ∧ PrimT.C4Geo.dR P ≤ P.n := by
    have := P.centerBits_sum
    change P.leftCenterBits ≤ P.n ∧ P.rightCenterBits ≤ P.n
    omega
  have he : SeedFix.callKh P ≤ P.n :=
    (Nat.mul_le_mul_left P.s (Nat.div_le_self P.r 2)).trans hk
  have hn : P.n < 2 ^ (P.n + 1) :=
    (Nat.lt_two_pow_self (n := P.n)).trans_le
      (Nat.pow_le_pow_right (by decide) (by omega))
  have hpow : 2 ^ P.n < 2 ^ (P.n + 1) :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  have ht : translationNumber P q.translation < 2 ^ P.n := by
    have h := (finFunctionFinEquiv (fun i : Fin P.r =>
      finFunctionFinEquiv (q.translation i))).isLt
    change translationNumber P q.translation < (2 ^ P.s) ^ P.r at h
    rw [← pow_mul] at h
    exact h.trans_le (Nat.pow_le_pow_right (by decide) hk)
  simp only [PointRequest.fields, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hn
  · exact hr.trans_lt hn
  · exact hb.trans_lt hn
  · exact hs.trans_lt hn
  · exact ht.trans hpow
  · exact (q.row.isLt.trans_le (Nat.pow_le_pow_right (by decide) hd.1)).trans hpow
  · exact (q.column.isLt.trans_le (Nat.pow_le_pow_right (by decide) hd.2)).trans hpow
  · exact (q.left.isLt.trans_le (Nat.pow_le_pow_right (by decide) he)).trans hpow
  · exact (q.right.isLt.trans_le (Nat.pow_le_pow_right (by decide) he)).trans hpow

/-- `prop:time`, paper/paper.tex: the physical
header parser requires only linear binary width in the input dimension. -/
theorem PointRequest.fields_bitLength (q : PointRequest) (v : ℕ) (hv : v ∈ q.fields) :
    natBitLength v ≤ q.parameters.n + 1 :=
  natBitLength_le_of_lt v _ (by omega) (q.fields_lt v hv)

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
distinct canonical scalar inputs occupy distinct retained variables. -/
def pointFieldRegister (i : Fin 9) : Fin VV := ⟨20 + i.val, by change 20 + i.val < 128; omega⟩

theorem pointFieldRegister_injective : Function.Injective pointFieldRegister := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  dsimp [pointFieldRegister] at this
  omega

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
the literal binary parser reads the complete compact header. -/
def pointFieldsProgram : St VV MM := StageGamma.readFields (List.ofFn pointFieldRegister)

/-- Step 4 of `sec:algorithm` and `prop:time`, paper/paper.tex: exact header parsing retains all nine scalar
values and leaves the cursor at the two physical corner-selection bits. -/
theorem pointFields_prefix (C : Ctx) (q : PointRequest) (rest : List Bool)
    (hinput : C.inp = q.fields.flatMap natWord ++ rest) (hwidth : q.parameters.n + 3 ≤ C.Wd)
    (a : DS VV MM) (hc : Cst a) (hip : a.ip = 0) :
    Hs C pointFieldsProgram a (StageGamma.readFieldsCost q.fields) (fun b =>
      (∀ i : Fin 9, b.env (pointFieldRegister i) =
        q.fields[i.val]'(by rw [PointRequest.fields_length]; exact i.isLt)) ∧
      b.ip = (q.fields.flatMap natWord).length ∧
      (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.out, a.ram, a.rc, a.kin, a.kout, a.kc) ∧ Cst b ∧
      Fr a b (List.ofFn pointFieldRegister ++ vJ :: rdNatT)) := by
  have hs : ∀ x ∈ List.ofFn pointFieldRegister, x ∉ vJ :: rdNatT ∧ x ∉ [vZ, v1, v2] := by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    simp only [rdNatT, List.mem_cons, List.not_mem_nil, or_false, not_or,
      pointFieldRegister, vJ, vZ, v1, v2, t0, t1, t2, t3, t4, Fin.mk.injEq]
    omega
  have hh := StageGamma.readFields_spec C (List.ofFn pointFieldRegister)
    (List.nodup_ofFn.mpr pointFieldRegister_injective) hs q.fields
    (by simp [PointRequest.fields_length]) a hc rest
    (by simp [hinput, hip]) (by
      intro v hv
      have := q.fields_bitLength v hv
      omega)
  refine Hs.mono hh le_rfl ?_
  rintro b ⟨hb, hbip, hrest, hbc, hfr⟩
  refine ⟨?_, by simpa [hip] using hbip, hrest, hbc, hfr⟩
  intro i
  simpa only [Fin.getElem_fin, List.getElem_ofFn] using
    hb ⟨i.val, by simpa only [List.length_ofFn] using i.isLt⟩

/-- Step 4 of `sec:algorithm` and `prop:time`, paper/paper.tex: the compact point parser leaves its cursor
at the two physical corner-selection bits. -/
theorem pointFields_parse (C : Ctx) (q : PointRequest)
    (hinput : C.inp = q.word) (hwidth : q.parameters.n + 3 ≤ C.Wd)
    (a : DS VV MM) (hc : Cst a) (hip : a.ip = 0) :
    Hs C pointFieldsProgram a (StageGamma.readFieldsCost q.fields) (fun b =>
      (∀ i : Fin 9, b.env (pointFieldRegister i) =
        q.fields[i.val]'(by rw [PointRequest.fields_length]; exact i.isLt)) ∧
      b.ip = (q.fields.flatMap natWord).length ∧
      (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.out, a.ram, a.rc, a.kin, a.kout, a.kc) ∧ Cst b ∧
      Fr a b (List.ofFn pointFieldRegister ++ vJ :: rdNatT)) :=
  pointFields_prefix C q [q.useLeft, q.useRight] (by rw [q.fields_word]; exact hinput)
    hwidth a hc hip

end NearQuarticWires.StagePullback
