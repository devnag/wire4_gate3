import Proof.Quartic.StageGamma.BankRecipe

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageGamma

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Cells
open NearCubicWires.WireExponent3_5

/-- `cor:conditional`, paper/paper.tex: exactly
eight base-`Q+1` digits, outside every serializer scratch variable. -/
def gammaDigit (slot : Fin 8) : Fin VV := ⟨40 + slot.val, by change 40 + slot.val < 128; omega⟩

/-- `cor:conditional`, paper/paper.tex: the selected
sample labels retain the true digit minus one, without field padding. -/
def gammaLabel (slot : Fin 8) : Fin VV := ⟨70 + slot.val, by change 70 + slot.val < 128; omega⟩

/-- `cor:conditional`, paper/paper.tex: the packed
walk-cell numbers computed from the ORIGINAL eight input vertices. -/
def gammaCell (slot : Fin 8) : Fin VV := ⟨80 + slot.val, by change 80 + slot.val < 128; omega⟩

/-- `cor:conditional`, paper/paper.tex: the cell
projection width is twice the ORIGINAL side-length exponent. -/
def gammaCellWidth : Fin VV := ⟨60, by decide⟩

/-- `cor:conditional`, paper/paper.tex: the actual
constraint writer skips zero digits and emits one exact equation otherwise. -/
def consSlotRecipe (slot : Fin 8) : Writer :=
  .nonzero (gammaDigit slot)
    (.seq (.literal [true])
      (.seq (Writer.binaryWord (requestFieldRegister 0) (gammaLabel slot)).framed
        (Writer.binaryWord gammaCellWidth (gammaCell slot)).framed))

/-- `cor:conditional`, paper/paper.tex: all eight
possible selected equations are followed by the literal end marker. -/
def consRecipe : Writer :=
  .seq (Writer.join (List.ofFn consSlotRecipe)) (.literal [false])

/-- `cor:conditional`, paper/paper.tex: the entire
equation writer preserves the source fields, modulus and radix digits. -/
theorem consRecipe_safe : consRecipe.Safe := by
  simp only [consRecipe, Writer.Safe, Writer.safe_join, List.mem_ofFn, forall_exists_index,
    forall_apply_eq_imp_iff]
  constructor
  · intro slot
    fin_cases slot <;>
      simp [consSlotRecipe, Writer.Safe, Writer.safe_framed, Writer.binaryWord,
        requestFieldRegister, gammaDigit, gammaLabel, gammaCell, gammaCellWidth,
        writerScratch, binaryScratch, emitIndex, binaryIndex, binaryWork, binaryQuot,
        binaryRem, vJ, vZ]
  · trivial

/-- `cor:conditional`, paper/paper.tex: one original
radix digit selects exactly the empty event or its true sample index. -/
theorem gammaChoiceCons_flatMap (P : Cycle.SeedParameters) (w : Cycle.Walk P.N 4)
    (choice : Cycle.GammaChoice P.Q) :
    Cycle.gammaChoiceCons P w choice = (List.finRange 8).flatMap (fun slot =>
      if (choice slot).val = 0 then [] else
        [((choice slot).val - 1,
          Sampler.cellNum P (Cycle.edge (by norm_num) w slot))]) := by
  unfold Cycle.gammaChoiceCons
  induction List.finRange 8 with
  | nil => rfl
  | cons slot slots ih =>
    rw [List.filterMap_cons, List.flatMap_cons, ih]
    have hh : ∀ digit : Fin (P.Q + 1),
        ((Cycle.sampleChoice digit).map fun j =>
          ((j : ℕ), Sampler.cellNum P (Cycle.edge (by norm_num) w slot))).toList =
        if digit.val = 0 then [] else
          [(digit.val - 1, Sampler.cellNum P (Cycle.edge (by norm_num) w slot))] := by
      intro digit
      refine Fin.cases ?_ (fun j => ?_) digit
      · rfl
      · simp [Cycle.sampleChoice]
    cases hc : Cycle.sampleChoice (choice slot) <;>
      simpa [hc] using congrArg (fun xs => xs ++
        slots.flatMap (fun i => if (choice i).val = 0 then [] else
          [((choice i).val - 1, Sampler.cellNum P (Cycle.edge (by norm_num) w i))]))
        (hh (choice slot))

/-- `cor:conditional`, paper/paper.tex: decoded
digits and physically computed labels/cells print precisely the unpadded
Gaussian constraint source for the ORIGINAL walk. -/
theorem consRecipe_bits (request : Machine.GammaRequest)
    (choice : Cycle.GammaChoice request.parameters.Q) (a : DS VV MM)
    (hell : a.env (requestFieldRegister 0) = request.parameters.ell)
    (hk : a.env gammaCellWidth = 2 * request.parameters.kh)
    (hd : ∀ slot, a.env (gammaDigit slot) = (choice slot).val)
    (hl : ∀ slot, a.env (gammaLabel slot) = (choice slot).val - 1)
    (hc : ∀ slot, a.env (gammaCell slot) =
      Sampler.cellNum request.parameters (Cycle.edge (by norm_num) request.walk slot)) :
    consRecipe.bits a = SeedFix.consTape request.parameters.ell (2 * request.parameters.kh)
      (conjunction request choice) [] := by
  simp only [consRecipe, Writer.bits, Writer.bits_join, List.ofFn_eq_map,
    List.flatMap_map, Function.comp_def]
  rw [SeedFix.consTape, conjunction, gammaChoiceCons_flatMap, List.flatMap_assoc]
  congr 1
  apply congrArg (List.flatMap · (List.finRange 8))
  funext slot
  simp only [consSlotRecipe, Writer.bits, hd]
  split_ifs <;>
    simp [Writer.bits_framed, Writer.bits_binaryWord, Writer.bits, hell, hk, hl, hc,
      SeedFix.consRec, List.append_assoc]

/-- `cor:conditional`, paper/paper.tex: the completed
bank producer has a fixed safe control independent of Q and the seed. -/
def gammaBankWriter : Writer := bankRecipe consRecipe

/-- `cor:conditional`, paper/paper.tex: all scratch
and source-variable disjointness for the actual bank are discharged. -/
theorem gammaBankWriter_safe : gammaBankWriter.Safe :=
  bankRecipe_safe consRecipe consRecipe_safe

end NearQuarticWires.StageGamma
