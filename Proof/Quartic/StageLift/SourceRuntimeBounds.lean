import Proof.Quartic.StageLift.SourceArithmetic
import Proof.Quartic.StageLift.SourceGuards
import Proof.Quartic.StageLift.SourceMetadata

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces

/-- Step 3 and `prop:time`, paper/paper.tex: the all-walk binary counter is controlled by the
selected partition width, not the Gamma table's byte length. -/
theorem source_walk_counter_bits {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    natBitLength (r.child.cellCall.seed.N ^ 8) ≤ 8 * sourceEnvelope r + 1 := by
  have hs := Cells.prepare_spec _ r.child.selected.1 r.child.selected.2
  have hN : r.child.cellCall.seed.N = 2 ^ (r.child.selected.1.k / 2) :=
    hs.seed_N.trans hs.N_eq
  have hk := (sourceEnvelope_bounds r).partition
  have hd : r.child.selected.1.k / 2 ≤ sourceEnvelope r :=
    (Nat.div_le_self _ _).trans hk
  rw [hN, ← pow_mul]
  have hlt : 2 ^ ((r.child.selected.1.k / 2) * 8) <
      2 ^ ((r.child.selected.1.k / 2) * 8 + 1) :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  have hb := NearCubicGates.Close.WorkerArith.WorkerBounds.nbl_le_of_lt
    (show 0 < (r.child.selected.1.k / 2) * 8 + 1 by omega) hlt
  omega

/-- `lem:print`, paper/paper.tex: the two actual
index-list counters fit the selected binary workspace even when their
signed target magnitudes are unrestricted. -/
theorem source_index_counter_bounds {B1 B2 : ℕ} (C : Ctx) (r : Greedy.PrintRequest B1 B2)
    (hW : 100 * (sourceEnvelope r + 1) ^ 2 ≤ C.Wd) :
    (natBitLength (printDigitList r).length + 2 ≤ C.Wd ∧
      natBitLength (printResidueList r).length + 2 ≤ C.Wd) ∧
    ((printDigitList r).length < 2 ^ C.Wd ∧ (printResidueList r).length < 2 ^ C.Wd) := by
  have hJ := (sourceEnvelope_bounds r).chains
  have hsmall : sourceEnvelope r + 1 ≤ (sourceEnvelope r + 1) ^ 2 := Nat.le_self_pow (by decide) _
  have hd := nbl_le_self (printDigitList r).length
  have hr := nbl_le_self (printResidueList r).length
  rw [print_digit_count] at hd ⊢
  rw [printResidueList_length] at hr ⊢
  have hWpow : C.Wd < 2 ^ C.Wd := Nat.lt_two_pow_self
  omega

/-- `lem:print` and `prop:time`, paper/paper.tex: all actual metadata reads and arithmetic are justified
by the original source envelope and its fixed header allocation. -/
theorem initializePrintMetadata_selected_source_spec {B1 B2 : ℕ} (C : Ctx)
    (r : Greedy.PrintRequest B1 B2) (a : DS VV MM) (hc : Cst a)
    (ha : PrintRequestData r a)
    (hempty : a.ram patternStore = [] ∧ a.rc patternStore = 0)
    (hW : 100 * (sourceEnvelope r + 1) ^ 2 ≤ C.Wd) :
    Hs C initializePrintMetadata a
      (a.rc parameterStore + a.rc indexStore + a.rc callStore + a.rc gammaStore +
        30 * natBitLength r.child.call.n +
        30 * natBitLength (kindTag r.child.call.kind) +
        30 * natBitLength (r.child.cellCall.seed.N ^ 8) + 1918) (fun b =>
      b.env degreeVar = residueDegreeBound r.child.selected.1 r.prime ∧
      b.env printArityVar = 17 * (Builder.allGates r.child.call).length ∧
      b.env degreeExponent = r.child.selected.1.e ∧
      b.env degreeChain = r.child.selected.1.J ∧ b.env degreePrime = r.prime ∧
      b.env signCodeVar = printPatternCode r.pattern ∧
      b.env callKindVar = kindTag r.child.call.kind ∧
      b.env printWalkIndex = 0 ∧ b.env printWalkCount = r.child.cellCall.seed.N ^ 8 ∧
      b.env StageRecovery.modulusVar = r.prime ^ r.child.selected.1.e ∧
      b.env preparedLength = a.env preparedLength ∧
      (∀ store, store ≠ patternStore → b.ram store = a.ram store) ∧
      b.rc gammaStore = (natWord (r.child.cellCall.seed.N ^ 8)).length ∧
      (b.ip, b.out, b.kin, b.kout, b.kc) = (a.ip, a.out, a.kin, a.kout, a.kc) ∧ Cst b) := by
  have hb := sourceEnvelope_bounds r
  have hsmall : sourceEnvelope r + 1 ≤ (sourceEnvelope r + 1) ^ 2 := Nat.le_self_pow (by decide) _
  have hfour : sourceEnvelope r + 1 ≤ (sourceEnvelope r + 1) ^ 4 := Nat.le_self_pow (by decide) _
  have hG : 17 * (Builder.allGates r.child.call).length ≤ 100 * (sourceEnvelope r + 1) ^ 4 := by
    nlinarith only [hb.occurrences, hfour]
  have hcap : 256 < 2 ^ C.Wd := by
    have h : 2 ^ 9 ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by decide) (by omega)
    norm_num at h
    omega
  have hn := nbl_le_self r.child.call.n
  have hnE := Cells.ParameterArithmetic.preparation_envelope_arity B1 r.child.call.n
  have hnSource : r.child.call.n ≤ sourceEnvelope r := by dsimp [sourceEnvelope]; omega
  have hk : natBitLength (kindTag r.child.call.kind) ≤ 3 := by
    cases r.child.call.kind <;> decide
  have hwalk := source_walk_counter_bits r
  exact initializePrintMetadata_source_spec C r a hc ha hempty (by omega)
    (hG.trans_lt (source_polynomial_fits _ _ hW)) (source_degree_room C r hW)
    hcap (by omega) (by omega) (by omega)

/-- Step 3 and `prop:time`, paper/paper.tex: the original selected startup contract is preserved
when the exact first-Gamma cursor is omitted. -/
theorem initializePrintMetadata_selected_spec {B1 B2 : ℕ} (C : Ctx)
    (r : Greedy.PrintRequest B1 B2) (a : DS VV MM) (hc : Cst a)
    (ha : PrintRequestData r a)
    (hempty : a.ram patternStore = [] ∧ a.rc patternStore = 0)
    (hW : 100 * (sourceEnvelope r + 1) ^ 2 ≤ C.Wd) :
    Hs C initializePrintMetadata a
      (a.rc parameterStore + a.rc indexStore + a.rc callStore + a.rc gammaStore +
        30 * natBitLength r.child.call.n +
        30 * natBitLength (kindTag r.child.call.kind) +
        30 * natBitLength (r.child.cellCall.seed.N ^ 8) + 1918) (fun b =>
      b.env degreeVar = residueDegreeBound r.child.selected.1 r.prime ∧
      b.env printArityVar = 17 * (Builder.allGates r.child.call).length ∧
      b.env degreeExponent = r.child.selected.1.e ∧
      b.env degreeChain = r.child.selected.1.J ∧ b.env degreePrime = r.prime ∧
      b.env signCodeVar = printPatternCode r.pattern ∧
      b.env callKindVar = kindTag r.child.call.kind ∧
      b.env printWalkIndex = 0 ∧ b.env printWalkCount = r.child.cellCall.seed.N ^ 8 ∧
      b.env StageRecovery.modulusVar = r.prime ^ r.child.selected.1.e ∧
      b.env preparedLength = a.env preparedLength ∧
      (∀ store, store ≠ patternStore → b.ram store = a.ram store) ∧
      (b.ip, b.out, b.kin, b.kout, b.kc) = (a.ip, a.out, a.kin, a.kout, a.kc) ∧ Cst b) := by
  exact (initializePrintMetadata_selected_source_spec C r a hc ha hempty hW).mono le_rfl
    (fun _ ⟨hD,hV,he,hJ,hp,hs,hk,hi,hN,hq,hP,hr,_hcursor,hio,hc⟩ =>
      ⟨hD,hV,he,hJ,hp,hs,hk,hi,hN,hq,hP,hr,hio,hc⟩)

end NearQuarticWires.StageLift
