import Proof.Gates.Codec.Emit

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.Streaming
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close NearCubicGates.Close.Interfaces

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: the actual
support buffer copies the literal sorted variable codecs once, with a
canonical count, and then emits its complete outer frame delimiter. -/
def supportCopyProgram (src dst : Fin (ns + 1)) (R : Fin 8 ↪ Fin nr) : WM ns nr :=
  .seq (Codec.copyList false src dst R (Codec.copyNat false src dst R))
    (emitC dst (R 7) false)

/-- `prop:time`, paper/paper.tex: the support
buffer includes the parsed count, every literal variable-word copy and
the final physical delimiter in its exact source clock. -/
def supportCopyCost (support : List ℕ) : ℕ :=
  Codec.copyListCost support.length
    (support.map (fun v => 60 * (natWord v).length + 60)) + 8

/-- `lem:print`, paper/paper.tex: the copy
subroutine consumes exactly the real support list, preserves the entire
input stream and leaves its next cursor at the signed coefficient. -/
theorem supportCopyProgram_spec (cap : ℕ) (src dst : Fin (ns + 1)) (hne : src ≠ dst)
    (R : Fin 8 ↪ Fin nr) (support : List ℕ) (pre rest : List Bool) (σ : WState ns nr)
    (hst : σ.st src = pre ++ listWord natWord support ++ rest)
    (hsh : σ.sh src = pre.length) (ho : σ.sh dst = (σ.st dst).length)
    (hz : ∀ i : Fin 8, i ≠ 7 → σ.val (R i) = 0)
    (V : ℕ) (hVcap : V + 2 ≤ cap)
    (hpow : 2 ^ (natBitLength support.length + 1) ≤ cap) (hlen : support.length ≤ cap)
    (hwrite : support.length + σ.val (R 7) + 6 * natBitLength support.length + 6 ≤ cap)
    (houtput : σ.val (R 7) + (marks (listWord natWord support)).length ≤ V) :
    WExec cap (supportCopyProgram src dst R) σ
      (appendO ((appendO σ dst (R 7) (marks (listWord natWord support))).seth src
        (pre.length + (listWord natWord support).length)) dst (R 7) [false])
      (supportCopyCost support) := by
  let ok : WState ns nr → Prop := fun b => b.val (R 1) = 0 ∧ b.val (R 2) = 0
  have readys (i j : Fin 8) (hij : i ≠ j) : R i ≠ R j := R.injective.ne hij
  have e := Codec.copyList_spec cap false src dst hne R
    (Codec.copyNat false src dst R) natWord (fun v => 60 * (natWord v).length + 60) ok V
    (by intro b x hb; exact hb)
    (by
      intro b x hb
      simp only [ok, WState.setv_val, Function.update_of_ne (readys 1 0 (by decide)),
        Function.update_of_ne (readys 2 0 (by decide))]
      exact hb)
    (by
      intro b w hb
      simp only [ok, appendO, WState.setv_val, Function.update_of_ne (readys 1 7 (by decide)),
        Function.update_of_ne (readys 2 7 (by decide))]
      exact hb)
    support (by
      intro v _ pre' rest' b hb hin hip hop hbound
      exact Codec.copyNat_spec cap false src dst hne R v pre' rest' b hin hip hop hb.1 hb.2
        (by simp only [marks_length] at hbound; omega))
    pre rest σ ⟨hz 1 (by decide), hz 2 (by decide)⟩
    (by simpa [NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc] using hst)
    hsh ho hz hpow hlen hwrite houtput
  let b := (appendO σ dst (R 7) (marks (listWord natWord support))).seth src
    (pre.length + (listWord natWord support).length)
  have e' : WExec cap (Codec.copyList false src dst R (Codec.copyNat false src dst R)) σ b
      (Codec.copyListCost support.length
        (support.map (fun v => 60 * (natWord v).length + 60))) := by
    simpa [b, stp] using e
  have eF := Codec.emitBit_spec cap dst (R 7) false b
    (by simp [b, appendO, hne.symm, ho, List.length_append])
    (by simp only [b, WState.seth_val, appendO, WState.setv_val, Function.update_self]
        omega)
  exact (e'.seq eF).cast cap rfl (by unfold supportCopyCost; omega)

end NearQuarticWires.StageTuple
