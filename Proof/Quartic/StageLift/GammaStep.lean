import Proof.Quartic.StageLift.GammaEnvelope
import Proof.Quartic.StageLift.GammaToken
import Proof.Quartic.StageLift.GammaWalk

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces
open NearCubicGates.Close.Interfaces.Formats

/-- Step 3 and `cor:conditional`, paper/paper.tex: the actual cursor after precisely the first k original
signed Gamma fields, following the physically decoded list header. -/
noncomputable def gammaByteCursor {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (k : ℕ) : ℕ :=
  (natWord (r.child.cellCall.seed.N ^ 8)).length +
    (((Greedy.gammaTable r.child).take k).flatMap NearCubicGates.Close.Interfaces.intWord).length

/-- Step 3, `sec:algorithm`, paper/paper.tex: before the first
walk, no Gamma integer has yet been consumed. -/
theorem gammaByteCursor_zero {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    gammaByteCursor r 0 = (natWord (r.child.cellCall.seed.N ^ 8)).length := by
  simp [gammaByteCursor]

/-- Step 3, `sec:algorithm`, paper/paper.tex: the next physical
Gamma cursor advances by exactly this original walk's integer codec. -/
theorem gammaByteCursor_succ {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (k : ℕ) (hk : k < r.child.cellCall.seed.N ^ 8) :
    gammaByteCursor r (k + 1) = gammaByteCursor r k +
      (NearCubicGates.Close.Interfaces.intWord
        (r.child.cellCall.walkWeight r.child.seedPrefix (printWalkAt _ ⟨k, hk⟩))).length := by
  have hlen : k < (Greedy.gammaTable r.child).length := by rw [actualGamma_length]; exact hk
  unfold gammaByteCursor
  rw [List.take_succ_eq_append_getElem hlen, List.flatMap_append,
    List.flatMap_singleton, List.length_append, gammaTable_at r ⟨k, hk⟩]
  omega

/-- Step 3 and `cor:conditional`, paper/paper.tex: the next stored integer is the original requested walk
weight, with the entire remaining source suffix still present. -/
theorem gammaSource_at {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2)
    (k : ℕ) (hk : k < r.child.cellCall.seed.N ^ 8) :
    (listWord NearCubicGates.Close.Interfaces.intWord (Greedy.gammaTable r.child)).drop
      (gammaByteCursor r k) =
      NearCubicGates.Close.Interfaces.intWord
        (r.child.cellCall.walkWeight r.child.seedPrefix (printWalkAt _ ⟨k, hk⟩)) ++
      ((Greedy.gammaTable r.child).drop (k + 1)).flatMap NearCubicGates.Close.Interfaces.intWord := by
  have hlen : k < (Greedy.gammaTable r.child).length := by rw [actualGamma_length]; exact hk
  have hsplit : (Greedy.gammaTable r.child).flatMap NearCubicGates.Close.Interfaces.intWord =
      ((Greedy.gammaTable r.child).take k).flatMap NearCubicGates.Close.Interfaces.intWord ++
      NearCubicGates.Close.Interfaces.intWord
        (r.child.cellCall.walkWeight r.child.seedPrefix (printWalkAt _ ⟨k, hk⟩)) ++
      ((Greedy.gammaTable r.child).drop (k + 1)).flatMap NearCubicGates.Close.Interfaces.intWord := by
    conv_lhs => rw [← List.take_append_drop k (Greedy.gammaTable r.child)]
    rw [List.flatMap_append, List.drop_eq_getElem_cons hlen, List.flatMap_cons,
      List.append_assoc, gammaTable_at r ⟨k, hk⟩]
  rw [listWord, actualGamma_length, hsplit]
  rw [show gammaByteCursor r k = ((natWord (r.child.cellCall.seed.N ^ 8)) ++
    ((Greedy.gammaTable r.child).take k).flatMap NearCubicGates.Close.Interfaces.intWord).length by
      simp only [gammaByteCursor, List.length_append]]
  simp only [List.append_assoc]
  rw [← List.append_assoc, List.drop_left]

/-- Step 3, `sec:algorithm`, paper/paper.tex: reload the real side
for each walk before reading its actual Gamma integer. -/
def emitCurrentGammaWeight : St VV MM := .seq loadPrintPart emitGammaWeight

/-- Step 3 and `lem:print`, paper/paper.tex: one literal all-walk iteration physically reads, splits and
prints its original coefficient. The selected source envelope supplies
all arithmetic width; no Gamma-value or split-word input is added. -/
theorem emitCurrentGammaWeight_spec {B1 B2 : ℕ} (C : Ctx)
    (r : Greedy.PrintRequest B1 B2) (k : ℕ) (hk : k < r.child.cellCall.seed.N ^ 8)
    (a : DS VV MM) (hc : Cst a)
    (hindex : a.ram indexStore = normalizedPrintIndex r)
    (hgamma : a.ram gammaStore =
      (listWord NearCubicGates.Close.Interfaces.intWord (Greedy.gammaTable r.child)).map Bool.toNat)
    (hcursor : a.rc gammaStore = gammaByteCursor r k)
    (hwidth : 100 * (sourceEnvelope r + 1) ^ 2 ≤ C.Wd) :
    Hs C emitCurrentGammaWeight a
      (a.rc indexStore + 70 * ((sourceEnvelope r + 1) ^ 2) + 159) (fun b =>
      b.out = a.out ++ tokWord (.const
        (Greedy.splitWeight r.child.cellCall r.child.seedPrefix r.sign (printWalkAt _ ⟨k, hk⟩))) ∧
      b.rc gammaStore = gammaByteCursor r (k + 1) ∧
      b.ram = a.ram ∧
      (∀ store, store ≠ gammaStore → store ≠ indexStore → b.rc store = a.rc store) ∧
      (b.ip, b.kin, b.kout, b.kc) = (a.ip, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b (partVar :: gammaTokenScratch)) := by
  have hside : a.ram indexStore = r.sign.toNat ::
      ((List.ofFn r.pattern).map Bool.toNat ++ [r.prime] ++
        (printDigitList r ++ printResidueList r).map
          (fun z : ℤ => (z % (r.prime ^ r.child.selected.1.e : ℤ)).toNat)) := by
    simpa only [normalizedPrintIndex, List.cons_append, List.nil_append, List.append_assoc] using hindex
  have he := loadPrintPart_spec C r.sign _ a hc hside
  unfold emitCurrentGammaWeight
  refine (Hs.seq (t1 := a.rc indexStore + 3)
    (t2 := 70 * ((sourceEnvelope r + 1) ^ 2) + 155) he
    fun b ⟨hbside, hbrc, hbram, hbsh, hbc, hbfr⟩ => ?_).mono (by omega) (fun _ h => h)
  have hbcursor : b.rc gammaStore = gammaByteCursor r k := by
    rw [hbrc, Function.update_of_ne (by decide)]
    exact hcursor
  have hinput := gammaSource_at r k hk
  rw [← hbcursor] at hinput
  have hbits := print_gamma_binary_width r (printWalkAt _ ⟨k, hk⟩)
  have hpos : 1 ≤ (sourceEnvelope r + 1) ^ 2 := Nat.pow_pos (by omega)
  have hs := emitGammaWeight_spec C
    (listWord NearCubicGates.Close.Interfaces.intWord (Greedy.gammaTable r.child)) b hbc
    (by rw [hbram]; exact hgamma) r.sign hbside _ _ hinput (by omega) (by omega)
  refine hs.mono (by omega) ?_
  rintro d ⟨hdo, _hdv, hdcur, hdrest, hdc, hdfr⟩
  have hram : d.ram = b.ram := congrArg (fun t => t.2.1) hdrest
  have hrc : Function.update d.rc gammaStore 0 = Function.update b.rc gammaStore 0 :=
    congrArg (fun t => t.2.2.1) hdrest
  have hdsh : (d.ip, d.kin, d.kout, d.kc) = (b.ip, b.kin, b.kout, b.kc) :=
    congrArg (fun t => (t.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2)) hdrest
  have hbsmall : (b.ip, b.kin, b.kout, b.kc) = (a.ip, a.kin, a.kout, a.kc) :=
    congrArg (fun t => (t.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2)) hbsh
  have hbo : b.out = a.out := congrArg (fun t => t.2.1) hbsh
  refine ⟨?_, ?_, hram.trans hbram, ?_, hdsh.trans hbsmall, hdc,
    (hbfr.weaken (by simp)).trans (hdfr.weaken (by
      intro x hx
      exact List.mem_cons_of_mem _ hx))⟩
  · rw [hdo, hbo, splitMagnitude_eq]
    rfl
  · rw [hdcur, hbcursor, gammaByteCursor_succ r k hk]
  · intro store hg hi
    have h := congrFun hrc store
    simpa only [Function.update_of_ne hg, hbrc, Function.update_of_ne hi] using h

end NearQuarticWires.StageLift
