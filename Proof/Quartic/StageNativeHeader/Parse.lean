import Proof.Quartic.StageNativeHeader.EmitReady
import Proof.Quartic.StageNativeHeader.Arith

/-!
# Reading the five fields

Paper: `lem:print`, paper/paper.tex.

`parseP` reads the five binary fields `n, r, b, s, p` of the marked input into `rN … rP` (`ParseNat.readNatM`), the
head of the input stopping at the marked cut bytes (`parse_exec`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearQuarticWires.StageNativeHeader

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.Streaming (marks marks_append)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (readNatM readNatM_spec enc stp natWord_length)
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearQuarticWires.StagePrint NearQuarticWires.StagePrint.Downstream

variable {ns nr : ℕ} (cap : ℕ)

/-- Only the streams of `S` and the registers of `L` change. -/
structure SOnly (σ τ : WState ns nr) (S : List (Fin (ns + 1))) (L : List (Fin nr)) : Prop where
  st : ∀ i, i ∉ S → τ.st i = σ.st i
  sh : ∀ i, i ∉ S → τ.sh i = σ.sh i
  val : ∀ x, x ∉ L → τ.val x = σ.val x

theorem SOnly.refl (σ : WState ns nr) (S : List (Fin (ns + 1))) (L : List (Fin nr)) : SOnly σ σ S L :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem SOnly.trans {σ τ ρ : WState ns nr} {S : List (Fin (ns + 1))} {L : List (Fin nr)} (h1 : SOnly σ τ S L)
    (h2 : SOnly τ ρ S L) : SOnly σ ρ S L :=
  ⟨fun i hi => (h2.st i hi).trans (h1.st i hi), fun i hi => (h2.sh i hi).trans (h1.sh i hi),
    fun x hx => (h2.val x hx).trans (h1.val x hx)⟩

theorem SOnly.weaken {σ τ : WState ns nr} {S S' : List (Fin (ns + 1))} {L L' : List (Fin nr)} (h : SOnly σ τ S L)
    (hS : ∀ i ∈ S, i ∈ S') (hL : ∀ x ∈ L, x ∈ L') : SOnly σ τ S' L' :=
  ⟨fun i hi => h.st i (fun h' => hi (hS i h')), fun i hi => h.sh i (fun h' => hi (hS i h')),
    fun x hx => h.val x (fun h' => hx (hL x h'))⟩

/-! ## The scratch registers of the reader -/

def pf : Fin hnr := 5
def pc : Fin hnr := 6
def pp : Fin hnr := 7
def pt : Fin hnr := 8

/-- The cost of reading `x`. -/
def readCost (x : ℕ) : ℕ := (natBitLength x + 2) * (40 * 2 ^ natBitLength x + 40)

/-- Read one field into `v` (from `0`). -/
theorem readStep (i : Fin (ns + 1)) (v : Fin hnr) (hv : v ∉ [pf, pc, pp, pt]) (x : ℕ) (pre rest : List Bool)
    (σ : WState ns hnr) (hst : σ.st i = pre ++ marks (natWord x) ++ rest) (hsh : σ.sh i = pre.length)
    (hz : ∀ y ∈ [pf, pc, pp, pt, v], σ.val y = 0) (hcap : 2 ^ (natBitLength x + 1) ≤ cap) :
    ∃ τ, WExec cap (readNatM true i pf pc v pp pt) σ τ (readCost x) ∧ SOnly σ τ [i] [v] ∧
      τ.st i = σ.st i ∧ τ.sh i = pre.length + (marks (natWord x)).length ∧ τ.val v = x := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hv
  have e := readNatM_spec cap true i pf pc v pp pt (by decide) (Ne.symm hv.1) (by decide) (by decide)
    (Ne.symm hv.2.1) (by decide) (by decide) (Ne.symm hv.2.2.1) (by decide) hv.2.2.2 x pre rest σ
    (by simpa [NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc] using hst) hsh (hz pf (by simp)) (hz pc (by simp)) (hz pp (by simp)) (hz pt (by simp))
    (by rw [hz v (by simp)]; omega)
  refine ⟨_, e, ⟨fun j hj => by simp, fun j hj => by
    simp only [List.mem_singleton] at hj; simp [Function.update_of_ne hj], fun y hy => by
    simp only [List.mem_singleton] at hy; simp [Function.update_of_ne hy]⟩, by simp, by
    simp [stp, Streaming.marks]; omega, by simp [hz v (by simp)]⟩

/-! ## The five fields -/

/-- Read `n, r, b, s, p`. -/
noncomputable def parseP : WM hns hnr :=
  .seq (readNatM true sIN pf pc rN pp pt) (.seq (readNatM true sIN pf pc rR pp pt)
    (.seq (readNatM true sIN pf pc rB pp pt) (.seq (readNatM true sIN pf pc rS pp pt)
      (readNatM true sIN pf pc rP pp pt))))

/-- The cost of `parseP`. -/
def parseCost (r : NativeHeaderRequest) : ℕ :=
  readCost r.parameters.n + readCost r.parameters.r + readCost r.parameters.b + readCost r.parameters.s +
    readCost r.table.matrix.p + 4

theorem fieldsWord_eq (r : NativeHeaderRequest) : fieldsWord r = natWord r.parameters.n ++
    (natWord r.parameters.r ++ (natWord r.parameters.b ++ (natWord r.parameters.s ++ natWord r.table.matrix.p))) := by
  simp [fieldsWord]

/-- **Reading the five fields.** -/
theorem parse_exec (r : NativeHeaderRequest) (σ : WState hns hnr) (rest : List Bool)
    (hst : σ.st sIN = marks (fieldsWord r) ++ rest) (hsh : σ.sh sIN = 0)
    (hz : ∀ y ∈ [pf, pc, pp, pt, rN, rR, rB, rS, rP], σ.val y = 0)
    (hcap : ∀ x ∈ [r.parameters.n, r.parameters.r, r.parameters.b, r.parameters.s, r.table.matrix.p],
      2 ^ (natBitLength x + 1) ≤ cap) :
    ∃ τ, WExec cap parseP σ τ (parseCost r) ∧ SOnly σ τ [sIN] [rN, rR, rB, rS, rP] ∧ τ.st sIN = σ.st sIN ∧
      τ.sh sIN = (marks (fieldsWord r)).length ∧ τ.val rN = r.parameters.n ∧ τ.val rR = r.parameters.r ∧
      τ.val rB = r.parameters.b ∧ τ.val rS = r.parameters.s ∧ τ.val rP = r.table.matrix.p := by
  set n := r.parameters.n with hn
  set rr := r.parameters.r with hrr
  set b := r.parameters.b with hb
  set s := r.parameters.s with hs
  set p := r.table.matrix.p with hp
  have hf : σ.st sIN = [] ++ marks (natWord n) ++
      (marks (natWord rr) ++ marks (natWord b) ++ marks (natWord s) ++ marks (natWord p) ++ rest) := by
    rw [hst, fieldsWord_eq]; simp only [marks_append, List.nil_append, List.append_assoc] <;> rfl
  obtain ⟨τ1, e1, f1, s1, h1, v1⟩ := readStep cap sIN rN (by decide) n [] _ σ hf (by simp [hsh])
    (fun y hy => hz y (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hy ⊢; tauto))
    (hcap n (by simp))
  have g1 : τ1.st sIN = marks (natWord n) ++ marks (natWord rr) ++
      (marks (natWord b) ++ marks (natWord s) ++ marks (natWord p) ++ rest) := by
    rw [s1, hf]; simp
  have z1 : ∀ y ∈ [pf, pc, pp, pt, rR, rB, rS, rP], τ1.val y = 0 := fun y hy => by
    rw [f1.val y (by revert hy; revert y; decide)]
    exact hz y (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hy ⊢; tauto)
  obtain ⟨τ2, e2, f2, s2, h2, v2⟩ := readStep cap sIN rR (by decide) rr _ _ τ1 g1 (by rw [h1]; simp <;> omega)
    (fun y hy => z1 y (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hy ⊢; tauto))
    (hcap rr (by simp))
  have g2 : τ2.st sIN = marks (natWord n) ++ marks (natWord rr) ++ marks (natWord b) ++
      (marks (natWord s) ++ marks (natWord p) ++ rest) := by
    rw [s2, g1]; simp
  have z2 : ∀ y ∈ [pf, pc, pp, pt, rB, rS, rP], τ2.val y = 0 := fun y hy => by
    rw [f2.val y (by revert hy; revert y; decide)]
    exact z1 y (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hy ⊢; tauto)
  obtain ⟨τ3, e3, f3, s3, h3, v3⟩ := readStep cap sIN rB (by decide) b _ _ τ2 g2 (by rw [h2]; simp <;> omega)
    (fun y hy => z2 y (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hy ⊢; tauto))
    (hcap b (by simp))
  have g3 : τ3.st sIN = marks (natWord n) ++ marks (natWord rr) ++ marks (natWord b) ++ marks (natWord s) ++
      (marks (natWord p) ++ rest) := by
    rw [s3, g2]; simp
  have z3 : ∀ y ∈ [pf, pc, pp, pt, rS, rP], τ3.val y = 0 := fun y hy => by
    rw [f3.val y (by revert hy; revert y; decide)]
    exact z2 y (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hy ⊢; tauto)
  obtain ⟨τ4, e4, f4, s4, h4, v4⟩ := readStep cap sIN rS (by decide) s _ _ τ3 g3 (by rw [h3]; simp <;> omega)
    (fun y hy => z3 y (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hy ⊢; tauto))
    (hcap s (by simp))
  have g4 : τ4.st sIN = marks (natWord n) ++ marks (natWord rr) ++ marks (natWord b) ++ marks (natWord s) ++
      marks (natWord p) ++ rest := by
    rw [s4, g3]; simp
  have z4 : ∀ y ∈ [pf, pc, pp, pt, rP], τ4.val y = 0 := fun y hy => by
    rw [f4.val y (by revert hy; revert y; decide)]
    exact z3 y (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hy ⊢; tauto)
  obtain ⟨τ5, e5, f5, s5, h5, v5⟩ := readStep cap sIN rP (by decide) p _ _ τ4 g4 (by rw [h4]; simp <;> omega)
    (fun y hy => z4 y (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hy ⊢; tauto))
    (hcap p (by simp))
  have F := ((((f1.weaken (S' := [sIN]) (by simp) (L' := [rN, rR, rB, rS, rP]) (by simp)).trans
    (f2.weaken (by simp) (by simp))).trans (f3.weaken (by simp) (by simp))).trans
    (f4.weaken (by simp) (by simp))).trans (f5.weaken (by simp) (by simp))
  refine ⟨τ5, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))) (by
    unfold parseCost; rw [← hn, ← hrr, ← hb, ← hs, ← hp]; omega), F, by rw [s5, s4, s3, s2, s1], ?_, ?_, ?_, ?_, ?_, v5⟩
  · rw [h5, fieldsWord_eq, ← hn, ← hrr, ← hb, ← hs, ← hp]; simp [marks_append]; omega
  · rw [f5.val _ (by decide), f4.val _ (by decide), f3.val _ (by decide), f2.val _ (by decide), v1]
  · rw [f5.val _ (by decide), f4.val _ (by decide), f3.val _ (by decide), v2]
  · rw [f5.val _ (by decide), f4.val _ (by decide), v3]
  · rw [f5.val _ (by decide), v4]

end NearQuarticWires.StageNativeHeader
