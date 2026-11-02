import Proof.Quartic.StageMain.EntryEmit

set_option autoImplicit false

namespace NearQuarticWires.StageMainMask

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open StageMain.Controller

/-- Step 4 of `sec:algorithm`, paper/paper.tex:
a fixed list of retained scalar registers is written in the literal
binary natural codec to the actual ordinary subroutine input. -/
def emitNaturalFields : List (Fin VV × ℕ) → St VV MM
  | [] => .op (.zero t3)
  | p :: ps => .seq (emitEntryNatural p.1) (emitNaturalFields ps)

/-- `prop:time`, paper/paper.tex: the scalar
request writer pays each binary printer and each sequential join. -/
def naturalFieldsCost : List (Fin VV × ℕ) → ℕ
  | [] => 1
  | p :: ps => 40 * natBitLength p.2 + 42 + naturalFieldsCost ps + 1

/-- Step 4 of `sec:algorithm` and `prop:time`, paper/paper.tex: actual retained scalars are copied
to the native call input with their exact binary bytes and charged
physical clock, while original source stores remain untouched. -/
theorem emitNaturalFields_run (C : Ctx) (fields : List (Fin VV × ℕ))
    (hregs : ∀ p ∈ fields, p.1 ∉ t3 :: emitNatT)
    (a : DS VV MM) (hc : Cst a) (hvalues : ∀ p ∈ fields, a.env p.1 = p.2)
    (hW : 2 ≤ C.Wd) (hfit : ∀ p ∈ fields, natBitLength p.2 + 2 < 2 ^ C.Wd)
    (hroom : a.kin.length + (fields.flatMap fun p => natWord p.2).length ≤ C.Lk) :
    Hs C (emitNaturalFields fields) a (naturalFieldsCost fields) (fun b =>
      b.kin = a.kin ++ fields.flatMap (fun p => natWord p.2) ∧
      (b.ip, b.out, b.ram, b.rc, b.kout, b.kc) =
        (a.ip, a.out, a.ram, a.rc, a.kout, a.kc) ∧ Cst b ∧ Fr a b (t3 :: emitNatT)) := by
  induction fields generalizing a with
  | nil =>
    refine (hs_zero C t3 a).mono le_rfl ?_
    rintro b rfl
    have hf : Fr a (a.set t3 0) (t3 :: emitNatT) := Fr.set a _ (by simp)
    exact ⟨by simp [DS.set], rfl, Cst.of_fr hc hf (by decide), hf⟩
  | cons p ps ih =>
    have hp := hregs p (by simp)
    unfold emitNaturalFields naturalFieldsCost
    refine Hs.seq (emitEntryNatural_run C p.1 (by
      intro heq; exact hp (by simp [heq])) a hc p.2 (hvalues p (by simp)) hW
      (hfit p (by simp)) (by simpa only [List.flatMap_cons, List.length_append] using
        (show a.kin.length + (natWord p.2).length ≤ C.Lk from by
          simp only [List.flatMap_cons, List.length_append] at hroom; omega))) ?_
    rintro b ⟨hbkin, hbrest, hbc, hbfr⟩
    refine (ih (fun q hq => hregs q (by simp [hq])) b hbc
      (fun q hq => (hbfr q.1 (hregs q (by simp [hq]))).trans (hvalues q (by simp [hq])))
      (fun q hq => hfit q (by simp [hq])) (by
        rw [hbkin, List.length_append]
        simpa only [List.flatMap_cons, List.length_append, Nat.add_assoc] using hroom)).mono le_rfl ?_
    rintro d ⟨hdkin, hdrest, hdc, hdfr⟩
    exact ⟨by rw [hdkin, hbkin, List.flatMap_cons, List.append_assoc],
      hdrest.trans hbrest, hdc, hbfr.trans hdfr⟩

end NearQuarticWires.StageMainMask
