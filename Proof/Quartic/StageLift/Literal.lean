import Proof.Quartic.StageRecovery.NaturalPrint
import Proof.Gates.Interfaces.CounterFormats

set_option autoImplicit false

namespace NearQuarticWires.StageLift

open NearCubicGates.Close.Cells
open NearCubicGates.Close.Interfaces.Formats

/-- `lem:print`, paper/paper.tex: fixed postfix
operation bytes are emitted by literal output instructions. -/
def emitLiteral : List Bool → St VV MM
  | [] => skipS
  | bit :: bits => .seq (.op (.emit bit)) (emitLiteral bits)

/-- `lem:print`, paper/paper.tex: every literal
byte is charged, and source cursors and retained arithmetic fields
survive the output operation. -/
theorem emitLiteral_spec (C : Ctx) (bits : List Bool) (a : DS VV MM) (hc : Cst a) :
    Hs C (emitLiteral bits) a (2 * bits.length + 1) (fun b =>
      b.out = a.out ++ bits ∧
      (b.ip, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.ip, a.ram, a.rc, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b [vJ]) := by
  induction bits generalizing a with
  | nil =>
    refine (skip_spec a).mono le_rfl ?_
    rintro b rfl
    exact ⟨by simp [DS.set], rfl,
      Cst.of_fr (T := [vJ]) hc (Fr.set a 0 (by simp)) (by decide),
      Fr.set a 0 (by simp)⟩
  | cons bit bits ih =>
    refine (Hs.seq (t2 := 2 * bits.length + 1) (hs_emit C bit a)
      fun b hb => ?_).mono (by simp; omega) (fun _ h => h)
    subst b
    have hcb : Cst ({ a with out := a.out ++ [bit] } : DS VV MM) :=
      ⟨hc.z, hc.one, hc.two⟩
    refine (ih _ hcb).mono le_rfl ?_
    rintro b ⟨ho, hr, hbc, hf⟩
    exact ⟨by simpa only [List.singleton_append, List.append_assoc] using ho,
      hr, hbc, hf⟩

/-- `lem:print`, paper/paper.tex: the fixed operator
tokens retain the published postfix token codec. -/
def emitOperator (token : Tok) : St VV MM := emitLiteral (tokWord token)

/-- `lem:print`, paper/paper.tex: a postfix operator
has exactly its original byte representation, with linear output cost. -/
theorem emitOperator_spec (C : Ctx) (token : Tok) (a : DS VV MM) (hc : Cst a) :
    Hs C (emitOperator token) a (2 * (tokWord token).length + 1) (fun b =>
      b.out = a.out ++ tokWord token ∧
      (b.ip, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.ip, a.ram, a.rc, a.kin, a.kout, a.kc) ∧
      Cst b ∧ Fr a b [vJ]) :=
  emitLiteral_spec C (tokWord token) a hc

end NearQuarticWires.StageLift
