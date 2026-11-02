import Proof.Quartic.StageTuplePreparedOutput.Cost

set_option autoImplicit false

namespace NearQuarticWires.StageTuplePreparedOutput

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open StageTuple StageTupleSetup

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: the
complete eleven-field prepared input is constructed from actual
retained sources and genuine helper caches, with one physical Terms
copy and exact final empty-field and outer-frame markers. -/
def preparedOutputProgram (P : Fin 10↪Fin (ns+1)) (R : Fin 4↪Fin nr) : WM ns nr :=
  .seq (headProgram P R) (finishProgram (suffixInstructions P) (P 9) (R 0) (R 1))

/-- `lem:print` and `prop:time`, paper/paper.tex: the whole genuine prepared formatter
has the exact eleven-field output, restores every other tape, head and
register, and charges the complete original Terms bytes only linearly. -/
theorem preparedOutputProgram_spec : StageTupleSetup.PreparedOutputSpec
    (ns:=ns) (nr:=nr) preparedOutputProgram := by
  intro cap P R r σ h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 hh hz hcap
  have hp : ∀ f∈prefixFields P r,
      f.source≠P 9 ∧ σ.st f.source=frame f.bits ∧ σ.sh f.source=0 := by
    intro f hf
    simp only [prefixFields, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl|rfl|rfl
    · exact ⟨P.injective.ne (by decide), h0, hh 0⟩
    · exact ⟨P.injective.ne (by decide), h1, hh 1⟩
    · exact ⟨P.injective.ne (by decide), h2, hh 2⟩
  have ht : ∀ f∈suffixFields P r,
      f.source≠P 9 ∧ σ.st f.source=frame f.bits ∧ σ.sh f.source=0 := by
    intro f hf
    simp only [suffixFields, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨P.injective.ne (by decide), h4, hh 4⟩
    · exact ⟨P.injective.ne (by decide), h5, hh 5⟩
    · exact ⟨P.injective.ne (by decide), h6, hh 6⟩
    · exact ⟨P.injective.ne (by decide), h7, hh 7⟩
    · exact ⟨P.injective.ne (by decide), h8, hh 8⟩
    · exact ⟨P.injective.ne (by decide), h4, hh 4⟩
  have ep := headProgram_spec cap P R r σ hp h3 (hh 3)
    (by rw [hh 9, h9]; rfl) (hz 1) (hz 2)
    (by simpa only [hz 0, Nat.zero_add] using (head_capacity P r).trans hcap)
  have et := finishProgram_spec cap (P 9) (R 0) (R 1)
    (R.injective.ne (by decide : (0 : Fin 4)≠1)) (suffixFields P r) (headBytes P r) σ
    ht h9 (hh 9) (hz 0) (hz 1) ((finish_capacity P r).trans hcap)
  have hbytes : headBytes P r++(suffixFields P r).flatMap CacheField.bytes++[true,false,false]=
      frame r.preparedWord := by
    simpa only [headBytes] using prepared_bytes P r
  simpa only [preparedOutputProgram, suffix_instructions, hbytes] using
    (ep.seq et).mono (prepared_clock_le P r)

end NearQuarticWires.StageTuplePreparedOutput
