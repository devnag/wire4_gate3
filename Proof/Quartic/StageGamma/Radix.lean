import Proof.Quartic.Machine.Enumeration
import Proof.Quartic.Cycle.GammaExpansion
import Proof.Gates.CounterMachine.CellTablesBody2
import Proof.Gates.Cells.Comp

set_option autoImplicit false

namespace NearQuarticWires.StageGamma

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.Cells
open NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.CounterMachine.CellTablesProg

/-- `cor:conditional`, paper/paper.tex: reversing the eight
slots reconciles the arithmetic decoder's most-significant-first order. -/
def reverseChoice (Q : ℕ) : Cycle.GammaChoice Q ≃ Cycle.GammaChoice Q where
  toFun a i := a i.rev
  invFun a i := a i.rev
  left_inv a := by funext i; simp
  right_inv a := by funext i; simp

/-- `cor:conditional`, paper/paper.tex: the exact radix
address space has precisely `(Q+1)^8` elements. -/
def radixChoiceEquiv (Q : ℕ) : Fin ((Q + 1) ^ 8) ≃ Cycle.GammaChoice Q :=
  finFunctionFinEquiv.symm.trans (reverseChoice Q)

/-- `cor:conditional`, paper/paper.tex: each decoded digit
is a constant-term or actual sample-label choice. -/
theorem radixChoice_digit (Q : ℕ) (address : Fin ((Q + 1) ^ 8)) (slot : Fin 8) :
    ((radixChoiceEquiv Q address slot : Fin (Q + 1)) : ℕ) =
      address.val / (Q + 1) ^ (7 - slot.val) % (Q + 1) := by
  change address.val / (Q + 1) ^ (8 - (slot.val + 1)) % (Q + 1) = _
  rw [show 8 - (slot.val + 1) = 7 - slot.val by omega]

/-- `cor:conditional`, paper/paper.tex: the eight words
emitted by the arithmetic decoder are the exact choice's eight coordinates. -/
theorem radixChoice_words (Q : ℕ) (address : Fin ((Q + 1) ^ 8)) :
    digs (Q + 1) address.val 8 =
      List.ofFn (fun slot : Fin 8 => (radixChoiceEquiv Q address slot).val) := by
  apply List.ext_getElem
  · simp [digs]
  · intro i hi hj
    simp only [digs, List.getElem_map, List.getElem_range, List.getElem_ofFn]
    rw [radixChoice_digit]

/-- `cor:conditional`, paper/paper.tex: one arithmetic
radix decoding has a linear cost in the radix's binary length. -/
def radixDecodeCost (Q : ℕ) : ℕ :=
  8 * (40 * natBitLength (Q + 1) + 64) + 4

/-- `prop:time`, paper/paper.tex: a computed capacity
accommodates the exact radix block, all existing stores and its input. -/
def radixCapacity (C : Ctx) (a : DS VV MM) (Q : ℕ) : ℕ :=
  2 * C.Wd + 2 + (2 * C.inp.length + 2) + a.out.length + radixDecodeCost Q +
    ((2 * C.Wd + 1) * ((∑ m : Fin MM, (a.ram m).length) + radixDecodeCost Q + 1) + 1) +
    (Rk C + 2)

/-- `prop:time`, paper/paper.tex: the physical compiler
needs no additional capacity promise for this explicitly reserved block. -/
theorem radixCapacity_ok (C : Ctx) (a : DS VV MM) (Q : ℕ) (hW : 1 ≤ C.Wd) :
    CapOK C (radixCapacity C a Q) a (radixDecodeCost Q) := by
  refine ⟨hW, by dsimp [radixCapacity]; omega, by dsimp [radixCapacity]; omega,
    by dsimp [radixCapacity]; omega, ?_, by dsimp [radixCapacity]; omega⟩
  intro m
  have hsum : (a.ram m).length ≤ ∑ j : Fin MM, (a.ram j).length :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (a.ram j).length) (Finset.mem_univ m)
  have := Nat.mul_le_mul_left (2 * C.Wd + 1)
    (Nat.add_le_add_right (Nat.add_le_add_right hsum (radixDecodeCost Q)) 1)
  dsimp [radixCapacity]
  omega

/-- `cor:conditional`, paper/paper.tex: the fixed
eight-digit decoder is an actual compiled multitape execution; its output
contains exactly the chosen sample indices and no field-label padding. -/
theorem radix_run (C : Ctx) (a : DS VV MM) (Q : ℕ)
    (address : Fin ((Q + 1) ^ 8))
    (hC : Cst a) (hW : 3 ≤ C.Wd) (hQ : 1 ≤ Q)
    (hq : a.env lQ = Q + 1) (ht : a.env lT = address.val)
    (hd : a.env kD = 8) (hb : a.env kB2 = Q + 1)
    (hp : a.env bPw = (Q + 1) ^ 8) (hk : a.env bKey = 0)
    (hfit : 2 * (Q + 1) ^ 8 ≤ 2 ^ C.Wd) (h8 : 8 < 2 ^ C.Wd)
    (hki : a.kin.length +
      ((List.ofFn fun slot : Fin 8 => (radixChoiceEquiv Q address slot).val).flatMap natWord).length ≤ C.Lk)
    (hB : ∀ s, C.K.bud s ≤ C.Bk → (C.K.outw s).length ≤ C.Bk + 3)
    (ha : Valid C a)
    (σ : WState (NS MM (TS C) VV) (NR MM)) (hσ : Enc C a σ) :
    ∃ (b : DS VV MM) (τ : WState (NS MM (TS C) VV) (NR MM)),
      Enc C b τ ∧
      WXExec (radixCapacity C a Q) (comp C.K digL) σ τ
        (radixDecodeCost Q * KC C) ∧
      b.kin = a.kin ++
        (List.ofFn fun slot : Fin 8 => (radixChoiceEquiv Q address slot).val).flatMap natWord ∧
      SameN a b ∧ Cst b ∧ Fr a b digT := by
  have hr := digL_spec C a hC hW (Q + 1) address.val 8 (Q + 1) 0
    (natBitLength (Q + 1)) (by omega) hq ht hd hb hp hk hfit h8 le_rfl
    (by simpa using (show (Q + 1) ^ 8 ≤ 2 ^ C.Wd by omega)) le_rfl
    (by simpa only [radixChoice_words] using hki)
  obtain ⟨b, n, hex, hn, hout, _, hsame, hc, hfr⟩ := hr
  have hcost : n ≤ radixDecodeCost Q := by simpa [radixDecodeCost] using hn
  have hex' := Ex.mono hex hcost
  obtain ⟨τ, henc, hrun⟩ := (comp_ok C (radixCapacity C a Q) hB hex' ha σ hσ
    (radixCapacity_ok C a Q (by omega))).1
  exact ⟨b, τ, henc, hrun, by simpa only [radixChoice_words] using hout, hsame, hc, hfr⟩

end NearQuarticWires.StageGamma
