import Proof.Quartic.StageLift.GammaWalk
import Proof.Quartic.StageLift.AritySource
import Proof.Quartic.StageLift.Token

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicWires NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Cells
open NearQuarticWires.StageRecovery

/-- `lem:print`, paper/paper.tex: a fixed list of
actual binary source registers is written in the unchanged natural codec. -/
def emitNaturalFields : List (Fin VV) → St VV MM
  | [] => skipS
  | field :: fields => .seq (emitVariable field) (emitNaturalFields fields)

/-- `lem:print`, paper/paper.tex: all scalar header
bits are physically serialized and charged; neither a precomputed header
word nor any decoded metadata provider is an input to this program. -/
theorem emitNaturalFields_spec (C : Ctx) (fields : List (Fin VV))
    (a : DS VV MM) (hc : Cst a) (B : ℕ)
    (hfields : ∀ x ∈ fields, x ∉ tokenScratch)
    (hbits : ∀ x ∈ fields, natBitLength (a.env x) ≤ B)
    (hW : 2 ≤ C.Wd) (hBit : B + 2 < 2 ^ C.Wd) :
    Hs C (emitNaturalFields fields) a (fields.length * (40 * B + 43) + 1) (fun b =>
      b.out = a.out ++ fields.flatMap (fun x => natWord (a.env x)) ∧
      (b.ip, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.ip, a.ram, a.rc, a.kin, a.kout, a.kc) ∧ Cst b ∧ Fr a b tokenScratch) := by
  induction fields generalizing a with
  | nil =>
    refine (skip_spec a).mono (by simp) ?_
    rintro b rfl
    exact ⟨by simp [DS.set], rfl,
      Cst.of_fr (T := [vJ]) hc (Fr.set _ _ (by simp)) (by decide),
      Fr.set _ _ (by decide)⟩
  | cons field fields ih =>
    have hfield : field ≠ t3 := by intro h; exact hfields field (by simp) (by simp [h, tokenScratch])
    have hb := hbits field (by simp)
    unfold emitNaturalFields
    refine (Hs.seq (t1 := 40 * natBitLength (a.env field) + 42)
      (t2 := fields.length * (40 * B + 43) + 1)
      (emitVariable_spec C a hc field hfield hW (by omega))
      fun b ⟨hbo, hbrest, hbc, hbfr⟩ => ?_).mono (by simp; nlinarith) (fun _ h => h)
    have hkeep (x : Fin VV) (hx : x ∈ field :: fields) : b.env x = a.env x := by
      apply hbfr
      intro hs
      apply hfields x hx
      simp only [tokenScratch, List.mem_cons, List.not_mem_nil, or_false] at hs ⊢
      tauto
    refine (ih b hbc (fun x hx => hfields x (by simp [hx]))
      (fun x hx => by rw [hkeep x (by simp [hx])]; exact hbits x (by simp [hx]))).mono le_rfl ?_
    rintro d ⟨hdo, hdrest, hdc, hdfr⟩
    have he : fields.flatMap (fun x => natWord (b.env x)) =
        fields.flatMap (fun x => natWord (a.env x)) := by
      apply List.flatMap_congr
      intro x hx
      rw [hkeep x (by simp [hx])]
    refine ⟨?_, hdrest.trans hbrest, hdc, (hbfr.weaken (by
      intro x hx
      simp only [tokenScratch, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      tauto)).trans hdfr⟩
    rw [hdo, hbo, he]
    simp only [List.flatMap_cons, List.append_assoc]

/-- `lem:print`, paper/paper.tex: the outer raw
packet starts with its real walk ordinal, degree, modulus and atom count. -/
def rawHeaderFields : List (Fin VV) := [printWalkIndex, degreeVar, modulusVar, printArityVar]

/-- `lem:print`, paper/paper.tex: the raw Formula
packet's scalar prefix is emitted before its actual framed postfix body. -/
def emitRawWalkHeader : St VV MM := emitNaturalFields rawHeaderFields

/-- `lem:print`, paper/paper.tex: exact binary
serialization of the four computed header registers preserves every
retained source and all live loop/Formula metadata. -/
theorem emitRawWalkHeader_spec (C : Ctx) (a : DS VV MM) (hc : Cst a) (B : ℕ)
    (hbits : ∀ x ∈ rawHeaderFields, natBitLength (a.env x) ≤ B)
    (hW : 2 ≤ C.Wd) (hBit : B + 2 < 2 ^ C.Wd) :
    Hs C emitRawWalkHeader a (4 * (40 * B + 43) + 1) (fun b =>
      b.out = a.out ++ natWord (a.env printWalkIndex) ++ natWord (a.env degreeVar) ++
        natWord (a.env modulusVar) ++ natWord (a.env printArityVar) ∧
      (b.ip, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.ip, a.ram, a.rc, a.kin, a.kout, a.kc) ∧ Cst b ∧ Fr a b tokenScratch) := by
  have hs := emitNaturalFields_spec C rawHeaderFields a hc B (by
    intro x hx
    rcases (by simpa only [rawHeaderFields, List.mem_cons, List.not_mem_nil, or_false] using hx) with
      rfl | rfl | rfl | rfl <;> decide) hbits hW hBit
  refine hs.mono le_rfl ?_
  rintro b ⟨hbo, hbrest, hbc, hbfr⟩
  exact ⟨by simpa only [rawHeaderFields, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.append_assoc] using hbo, hbrest, hbc, hbfr⟩

end NearQuarticWires.StageLift
