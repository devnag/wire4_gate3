import Proof.Quartic.Reconstruct.PrintLink2

/-!
# The printed tables in the order of the loop nest

Paper: Step 3 of `sec:algorithm`, paper/paper.tex.

`printList_flatMap`: the entries `frame (printIndexWord r) ++ frame (printInput r)` of all tables of `printList`, at
depth `1`, are the words written by the loop nest `partS` (`PrintNest3.partS_spec`) for the data of the child.
-/

set_option autoImplicit false

namespace NearQuarticWires.Reconstruct

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces (listWord bitWord)
open NearCubicWires.RepairOrdinary (frame)
open NearQuarticWires.Greedy NearQuarticWires.Program

variable {B1 B2 : ℕ}

/-- The entry of one table at depth `1`. -/
noncomputable def reqOut (r : PrintRequest B1 B2) : List Bool :=
  marksD 1 (frame (printIndexWord r) ++ frame (printInput r))

/-- The data of the request phase of a child. -/
noncomputable def rpOf (q : ChildRequest B1 B2) (ℓ : ℕ) : RP :=
  ⟨prepWord B1 B2 q.call q.witness, listWord NearCubicGates.Close.Interfaces.intWord (gammaTable q), baseOf q,
    q.cellCall.J + 1, q.selected.1.hE - 1, if pairBit q = 1 then q.selected.1.hE - 1 else 0, 2 * (q.cellCall.J + 1), ℓ⟩

/-- The data of the loop nest of a child. -/
noncomputable def npOf (q : ChildRequest B1 B2) (Pm : ℕ) : NP :=
  ⟨q.selected.1.primes.sort (· ≤ ·), pairBit q, Pm, baseOf q ^ (q.cellCall.J + 1), a1Of q⟩

theorem digitList_eq (q : ChildRequest B1 B2) :
    digitList q = (List.range (baseOf q ^ (q.cellCall.J + 1))).flatMap fun x0 => (List.range (a1Of q)).map fun x1 =>
      (![vecAt (digitL q) 0 (q.cellCall.J + 1) x0, dig1 q x1] : Fin 2 → Fin (q.cellCall.J + 1) → ℤ) := by
  classical
  unfold digitList
  rw [show ∀ (X Y : List (Fin (q.cellCall.J + 1) → ℤ)), X ×ˢ Y = X.flatMap (fun a => Y.map (Prod.mk a)) from
    fun _ _ => rfl, List.map_flatMap, digitAxisList_zero, List.flatMap_map]
  refine List.flatMap_congr fun x0 _ => ?_
  rw [List.map_map]
  unfold a1Of dig1 pairBit
  rw [digitAxisList_one]
  by_cases h : q.call.kind = .pair
  · simp only [if_pos h, if_true, List.map_map]
    rfl
  · simp only [if_neg h, show ¬((0 : ℕ) = 1) by decide, if_false, List.range_one, List.map_cons, List.map_nil]
    rfl

theorem residueListOf_eq (q : ChildRequest B1 B2) (p : ℕ) :
    residueListOf q p = (List.range p).flatMap fun y0 : ℕ => (List.range (resQ (pairBit q) p)).map fun y1 : ℕ =>
      (![(y0 : ℤ), (y1 : ℤ)] : Fin 2 → ℤ) := by
  classical
  unfold residueListOf
  rw [if_pos (zero_mem_circuitSet q.call)]
  rw [show ∀ (X Y : List ℤ), X ×ˢ Y = X.flatMap (fun a => Y.map (Prod.mk a)) from fun _ _ => rfl, List.map_flatMap,
    List.flatMap_map]
  refine List.flatMap_congr fun y0 _ => ?_
  rw [List.map_map]
  unfold resQ pairBit
  by_cases h : q.call.kind = .pair
  · rw [if_pos ((one_mem_circuitSet q.call).mpr h)]
    simp only [if_pos h, if_true, List.map_map]
    rfl
  · rw [if_neg (fun h' => h ((one_mem_circuitSet q.call).mp h'))]
    simp only [if_neg h, show ¬((0 : ℕ) = 1) by decide, if_false, List.range_one, List.map_cons, List.map_nil]
    rfl

theorem flatMap_attach_val {α β : Type} (l : List α) (g : α → List β) :
    l.attach.flatMap (fun p => g p.1) = l.flatMap g := by
  have : l.attach.map Subtype.val = l := List.attach_map_subtype_val l
  conv_rhs => rw [← this]
  rw [List.flatMap_map]

/-- The entry of a table from its data. -/
noncomputable def reqData (q : ChildRequest B1 B2) (s : Bool) (σ : Cycle.SignPattern Algorithm.traceOrder)
    (δ : Fin 2 → Fin (q.cellCall.J + 1) → ℤ) (p : ℕ) (ρ : Fin 2 → ℤ) : List Bool :=
  marksD 1 (frame (bitWord s ++ listWord bitWord (List.ofFn σ) ++ natWord p ++
      listWord NearCubicGates.Close.Interfaces.intWord (List.ofFn fun i : Fin 2 => List.ofFn fun j => δ i j).flatten ++
      listWord NearCubicGates.Close.Interfaces.intWord (List.ofFn ρ)) ++
    frame (prepWord B1 B2 q.call q.witness ++ gammaTableWord q ++ (bitWord s ++ listWord bitWord (List.ofFn σ) ++
      natWord p ++
      listWord NearCubicGates.Close.Interfaces.intWord (List.ofFn fun i : Fin 2 => List.ofFn fun j => δ i j).flatten ++
      listWord NearCubicGates.Close.Interfaces.intWord (List.ofFn ρ))))

theorem reqOut_printRequestOf (q : ChildRequest B1 B2) (s : Bool) (σ : Cycle.SignPattern Algorithm.traceOrder)
    (δ : Fin 2 → Fin (q.cellCall.J + 1) → ℤ) (p : {p // p ∈ primeList q.cellCall}) (ρ : Fin 2 → ℤ) :
    reqOut (printRequestOf q s σ δ p ρ) = reqData q s σ δ p.1 ρ := rfl

/-- The entry of one table of the counters. -/
theorem reqData_eq (q : ChildRequest B1 B2) (ℓ iS is x0 x1 p y0 y1 : ℕ)
    (hx0 : x0 < baseOf q ^ (q.cellCall.J + 1)) (hx1 : x1 < a1Of q) :
    reqData q (decide (iS = 0)) (vecAt [false, true] false 8 is)
        (![vecAt (digitL q) 0 (q.cellCall.J + 1) x0, dig1 q x1] : Fin 2 → Fin (q.cellCall.J + 1) → ℤ) p
        (![(y0 : ℤ), (y1 : ℤ)] : Fin 2 → ℤ) =
      rpWord (rpOf q ℓ) (if iS = 0 then 1 else 0) is x0 x1 p y0 y1 := by
  have hE : 1 ≤ q.selected.1.hE := by
    by_contra h
    have h0 : baseOf q = 0 := by unfold baseOf; omega
    rw [h0, zero_pow (by omega)] at hx0; omega
  have hx1' : pairBit q ≠ 1 → x1 = 0 := fun h => by unfold a1Of at hx1; rw [if_neg h] at hx1; omega
  have hfl : (List.ofFn fun i : Fin 2 => List.ofFn fun j : Fin (q.cellCall.J + 1) =>
      (![vecAt (digitL q) 0 (q.cellCall.J + 1) x0, dig1 q x1] : Fin 2 → Fin (q.cellCall.J + 1) → ℤ) i j).flatten =
      List.ofFn (vecAt (digitL q) 0 (q.cellCall.J + 1) x0) ++ List.ofFn (dig1 q x1) := by
    rw [digits_flatten]; rfl
  have hr : List.ofFn (![(y0 : ℤ), (y1 : ℤ)] : Fin 2 → ℤ) = [(y0 : ℤ), (y1 : ℤ)] := by simp
  have hI := index_marks q iS is x0 x1 p y0 y1 hE hx1'
  unfold reqData rpWord reqWord
  rw [hfl, hr]
  generalize hX : bitWord (decide (iS = 0)) ++ listWord bitWord (List.ofFn (vecAt [false, true] false 8 is)) ++
    natWord p ++ listWord NearCubicGates.Close.Interfaces.intWord
      (List.ofFn (vecAt (digitL q) 0 (q.cellCall.J + 1) x0) ++ List.ofFn (dig1 q x1)) ++
    listWord NearCubicGates.Close.Interfaces.intWord [(y0 : ℤ), (y1 : ℤ)] = X at hI
  rw [marksD_append, marksD_frame, marksD_frame, marksD_append, marksD_append]
  simp only [Nat.reduceAdd]
  rw [hI]
  unfold rpOf gammaTableWord
  simp only [List.append_assoc]

/-- **The tables of `printList` in the order of the loop nest.** -/
theorem printList_flatMap (q : ChildRequest B1 B2) (ℓ Pm : ℕ) :
    (printList q).flatMap reqOut = (List.range 2).flatMap fun iS => (List.range 256).flatMap fun is =>
      sigWord (rpOf q ℓ) (npOf q Pm) (if iS = 0 then 1 else 0) is := by
  unfold printList
  rw [List.flatMap_assoc, show [true, false] = (List.range 2).map (fun iS => decide (iS = 0)) from rfl,
    List.flatMap_map]
  refine List.flatMap_congr fun iS _ => ?_
  rw [List.flatMap_assoc, patternList_eq, List.flatMap_map]
  refine List.flatMap_congr fun is _ => ?_
  unfold sigWord
  rw [List.flatMap_assoc, digitList_eq, List.flatMap_assoc]
  refine List.flatMap_congr fun x0 hx0 => ?_
  rw [List.flatMap_map]
  refine List.flatMap_congr fun x1 hx1 => ?_
  rw [List.mem_range] at hx0 hx1
  rw [List.flatMap_assoc]
  simp only [List.flatMap_map, reqOut_printRequestOf]
  unfold dWord
  rw [flatMap_attach_val (primeList q.cellCall) (fun p => (residueListOf q p).flatMap fun a =>
    reqData q (decide (iS = 0)) (vecAt [false, true] false 8 is)
      (![vecAt (digitL q) 0 (q.cellCall.J + 1) x0, dig1 q x1] : Fin 2 → Fin (q.cellCall.J + 1) → ℤ) p a),
    show primeList q.cellCall = (npOf q Pm).ps from rfl]
  refine List.flatMap_congr fun p _ => ?_
  unfold primeWord
  rw [residueListOf_eq, List.flatMap_assoc]
  refine List.flatMap_congr fun y0 _ => ?_
  rw [List.flatMap_map]
  refine List.flatMap_congr fun y1 _ => ?_
  exact reqData_eq q ℓ iS is x0 x1 p y0 y1 hx0 hx1

end NearQuarticWires.Reconstruct
