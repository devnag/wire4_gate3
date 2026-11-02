import Proof.Quartic.StageGreedyEntry.HeaderRun
import Proof.Quartic.StageGreedyCollector.PerEntryTarget
import Proof.Quartic.StagePrint.GreedyEntryDock
import Proof.Gates.Expand.PolyTabPack

/-!
# The common header from the formatted entry: the word function

Paper: `lem:print`, paper/paper.tex.

The formatted entry `frame r.termRequest.word` is the eleven-field record of `hdr_run`: field 1 is `frame` of the
base header values `n, x₁, x₂, r, b, s, t` of the original call and its selected parameters, field 4 is the stack
width `W`. The star of the original request has `n`, `r`, `b`, `s` equal to these (`hd_globalHeader_eq`), and its
common field width is `W + 1` (`GreedyEntry.Request.fieldWidth_eq`). So `hdrP` maps the formatted entry to
`frame (globalHeader r.source)` (`headerWF`), within twice `hdrCostOf r` plus two.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageGreedyEntry

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.RepairRepresentation (natWord)
open StagePrint
open NearCubicWires.WireExponent3_5.CompilerMachine
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Tabulator NearCubicGates.Close.TabMachine

variable {B1 B2 : ℕ}

/-- The first base header value after the arity. -/
def hdX1 (r : GreedyEntry.Request B1 B2) : ℕ :=
  (4 * r.source.child.call.n + 1) * Nat.clog 2 (r.source.child.call.n + 1) + 5

/-- The cost of the header program on one entry. -/
noncomputable def hdrCostOf (r : GreedyEntry.Request B1 B2) : ℕ :=
  hdrCost r.termRequest.word.length r.source.child.call.n (hdX1 r) (hdX1 r + r.source.child.call.n + 6)
    r.source.child.selected.1.r r.source.child.selected.1.b r.source.child.selected.1.s r.termRequest.stackWidth

/-- The register capacity of the header program on one entry. -/
noncomputable def hdrCap (r : GreedyEntry.Request B1 B2) : ℕ :=
  2 * r.termRequest.word.length + 1 + 20 * (r.source.child.call.n + hdX1 r + (hdX1 r + r.source.child.call.n + 6) +
    r.source.child.selected.1.r + r.source.child.selected.1.b + r.source.child.selected.1.s +
    r.termRequest.stackWidth) + 200

/-- The formatted entry is the record of `hdr_run`. -/
theorem hd_termRequest_word_eq (r : GreedyEntry.Request B1 B2) :
    r.termRequest.word = frame (frame (callWord r.source.child.call)) ++
      (frame (frame ([r.source.child.call.n, hdX1 r, hdX1 r + r.source.child.call.n + 6,
        r.source.child.selected.1.r, r.source.child.selected.1.b, r.source.child.selected.1.s,
        StagePullback.translationNumber (Builder.star r.source.child.call (Context.header r.prepared).prepared)
          (Builder.translation r.source.child.call (Context.header r.prepared).prepared
            r.source.child.witness)].flatMap natWord)) ++
      (frame r.termRequest.contextWord ++ (frame (termsWord r.termRequest.terms) ++
        (frame (natWord r.termRequest.stackWidth) ++
          (frame (natWord r.termRequest.degree) ++ (frame [] ++ (frame [] ++ (frame [] ++
            (frame [] ++ frame []))))))))) := rfl

/-- **The common header** of the original request: its arity, the selected `r`, `b`, `s`, and the common field
width `W + 1`. -/
theorem hd_globalHeader_eq (r : GreedyEntry.Request B1 B2) :
    StageGreedyCollector.globalHeader r.source = [r.source.child.call.n, r.source.child.selected.1.r,
      r.source.child.selected.1.b, r.source.child.selected.1.s, r.termRequest.stackWidth + 1].flatMap natWord := by
  have hs := Cells.prepare_spec _ r.source.child.selected.1 r.source.child.selected.2
  have hb : (GreedyCollector.star r.source).b = r.source.child.selected.1.b := Cells.ParameterRules.star_b hs
  have hss : (GreedyCollector.star r.source).s = r.source.child.selected.1.s := Cells.ParameterRules.star_s hs
  have hw : GreedyCollector.fieldWidth r.source = r.termRequest.stackWidth + 1 :=
    (GreedyEntry.Request.fieldWidth_eq r).symm
  unfold StageGreedyCollector.globalHeader
  rw [hb, hss, hw]
  rfl

/-- **The header word function**: the formatted entry to the framed common header. -/
noncomputable def headerWF (B1 B2 : ℕ) :
    WordFunction (GreedyEntry.Request B1 B2) (fun r => frame r.termRequest.word)
      (fun r => frame (StageGreedyCollector.globalHeader r.source)) (fun r => 2 * hdrCostOf r + 2) :=
  NearCubicGates.Close.Expand.PolyTab.wordFunction_of_ideal (.wm hdrP) hdOUT (by decide) hdrCap
    (fun _ _ => 0) hdrCostOf (fun _ => le_refl _) (fun r => by
      refine ⟨rfl, ?_⟩
      obtain ⟨τ, e, hout⟩ := hdr_run (hdrCap r) (frame (callWord r.source.child.call)) r.termRequest.contextWord
        (termsWord r.termRequest.terms)
        (frame (natWord r.termRequest.degree) ++ (frame [] ++ (frame [] ++ (frame [] ++ (frame [] ++ frame [])))))
        r.source.child.call.n (hdX1 r) (hdX1 r + r.source.child.call.n + 6) r.source.child.selected.1.r
        r.source.child.selected.1.b r.source.child.selected.1.s
        (StagePullback.translationNumber (Builder.star r.source.child.call (Context.header r.prepared).prepared)
          (Builder.translation r.source.child.call (Context.header r.prepared).prepared r.source.child.witness))
        r.termRequest.stackWidth r.termRequest.word (hd_termRequest_word_eq r) (le_refl _)
      refine ⟨τ, WXExec.ofW (hdrCap r) e rfl (le_refl _), ?_⟩
      rw [hout, hd_globalHeader_eq])

end NearQuarticWires.StageGreedyEntry
