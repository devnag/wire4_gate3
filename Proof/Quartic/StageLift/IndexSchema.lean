import Proof.Quartic.Greedy.Child

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Interfaces

/-- `lem:print` and Step 3, paper/paper.tex: literal sign-pattern fields use the original natural Boolean
codec, not a one-bit or raw sign-bit surrogate. -/
theorem boolean_word_nat (b : Bool) : bitWord b = natWord b.toNat := by
  cases b <;> rfl

/-- `lem:print` and Step 3, paper/paper.tex: the actual counted pattern word is a list of natural bits. -/
theorem boolean_list_nat (bits : List Bool) :
    listWord bitWord bits = listWord natWord (bits.map Bool.toNat) := by
  have hf : bitWord = (fun b : Bool => natWord b.toNat) := by
    funext b
    exact boolean_word_nat b
  simp only [listWord, List.length_map, List.flatMap_map, hf]

/-- Step 3, `sec:algorithm`, paper/paper.tex: digit fields follow
the unchanged circuit-major, chain-minor original index order. -/
noncomputable def printDigitList {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : List ℤ :=
  (List.ofFn fun i : Fin 2 =>
    List.ofFn fun j : Fin (r.child.cellCall.J + 1) => r.digits i j).flatten

/-- Step 3, `sec:algorithm`, paper/paper.tex: both score residues
occur in their original circuit order. -/
def printResidueList {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : List ℤ :=
  List.ofFn r.residues

/-- `lem:print`, paper/paper.tex: the literal
header before the signed digit and score lists is small and self-delimiting. -/
def printIndexHeader {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) : List Bool :=
  natWord r.sign.toNat ++ listWord natWord ((List.ofFn r.pattern).map Bool.toNat) ++ natWord r.prime

/-- `lem:print`, paper/paper.tex: the complete
actual printer index word has its unchanged three header components
and two genuine signed integer lists. -/
theorem printIndexWord_layout {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    Greedy.printIndexWord r = printIndexHeader r ++
      listWord NearCubicGates.Close.Interfaces.intWord (printDigitList r) ++
      listWord NearCubicGates.Close.Interfaces.intWord (printResidueList r) := by
  simp only [Greedy.printIndexWord, printIndexHeader, printDigitList, printResidueList,
    boolean_word_nat, boolean_list_nat, List.append_assoc]

/-- `lem:print`, paper/paper.tex: exactly eight
natural pattern bits are present in the quartic trace-order index. -/
theorem print_pattern_length {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    ((List.ofFn r.pattern).map Bool.toNat).length = 8 := by
  simp [Algorithm.traceOrder]

/-- `lem:print`, paper/paper.tex: the actual
digit-list count is twice the original chain length including its endpoint. -/
theorem printDigitList_length {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    (printDigitList r).length = 2 * (r.child.cellCall.J + 1) := by
  simp [printDigitList]
  omega

/-- `lem:print`, paper/paper.tex: the actual
score-residue list has two entries even for an absent circuit. -/
theorem printResidueList_length {B1 B2 : ℕ} (r : Greedy.PrintRequest B1 B2) :
    (printResidueList r).length = 2 := by simp [printResidueList]

/-- `lem:residue`, paper/paper.tex: normalizing
an arbitrary raw digit modulo p^e retains its exact target modulo p
when the selected positive exponent makes p divide p^e. -/
theorem normalized_digit_target (prime e : ℕ) (he : 0 < e) (z : ℤ) :
    (z % (prime ^ e : ℕ)) % (prime : ℤ) = z % (prime : ℤ) := by
  apply Int.emod_emod_of_dvd
  exact_mod_cast dvd_pow_self prime (Nat.ne_of_gt he)

end NearQuarticWires.StageLift
