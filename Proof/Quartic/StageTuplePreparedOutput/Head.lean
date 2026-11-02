import Proof.Quartic.StageTuplePreparedOutput.Finish

set_option autoImplicit false

namespace NearQuarticWires.StageTuplePreparedOutput

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Interfaces
open NearCubicGates.Close.Interfaces.Formats
open StageTuple

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: the
first three real prepared fields have fixed retained source addresses. -/
def prefixInstructions (P : Fin 10↪Fin (ns+1)) : List (Fin (ns+1)×Bool) :=
  [(P 0,true),(P 1,true),(P 2,true)]

/-- `lem:print`, paper/paper.tex: the six
remaining real cache copies have fixed source addresses and framing choices. -/
def suffixInstructions (P : Fin 10↪Fin (ns+1)) : List (Fin (ns+1)×Bool) :=
  [(P 4,false),(P 5,true),(P 6,true),(P 7,false),(P 8,false),(P 4,true)]

/-- `lem:print`, paper/paper.tex: the
original retained fields are followed by one physical original Terms copy. -/
def headProgram (P : Fin 10↪Fin (ns+1)) (R : Fin 4↪Fin nr) : WM ns nr :=
  .seq (cachesProgram (prefixInstructions P) (P 9) (R 0) (R 1))
    (termsProgram (P 3) (P 9) (R 0) (R 1) (R 2))

/-- `lem:print`, paper/paper.tex: the
prefix contains the original three real fields and the whole Terms once. -/
def headBytes (P : Fin 10↪Fin (ns+1)) (r : TermCutRequest) : List Bool :=
  (prefixFields P r).flatMap CacheField.bytes++marks (frame (termsWord r.terms))

/-- `prop:time`, paper/paper.tex: the
prefix clock is additive in retained small caches and actual source bytes. -/
def headClock (P : Fin 10↪Fin (ns+1)) (r : TermCutRequest) : ℕ :=
  cachesClock (prefixFields P r)+1+500*((originalPrefix r).length+(frame (termsWord r.terms)).length+1)

/-- `lem:print`, paper/paper.tex: semantic
payload data do not enter the fixed prefix-copy instruction list. -/
theorem prefix_instructions (P : Fin 10↪Fin (ns+1)) (r : TermCutRequest) :
    (prefixFields P r).map CacheField.instruction=prefixInstructions P := rfl

/-- `lem:print`, paper/paper.tex: semantic
payload data do not enter the fixed suffix-copy instruction list. -/
theorem suffix_instructions (P : Fin 10↪Fin (ns+1)) (r : TermCutRequest) :
    (suffixFields P r).map CacheField.instruction=suffixInstructions P := rfl

/-- `lem:print` and `prop:time`, paper/paper.tex: actual source tapes supply the prepared
prefix and its single Terms field, preserving every source and scratch
component while charging the complete Terms only linearly. -/
theorem headProgram_spec (cap : ℕ) (P : Fin 10↪Fin (ns+1)) (R : Fin 4↪Fin nr)
    (r : TermCutRequest) (σ : WState ns nr)
    (hsrc : ∀ f∈prefixFields P r,
      f.source≠P 9 ∧ σ.st f.source=frame f.bits ∧ σ.sh f.source=0)
    (hs3 : σ.st (P 3)=r.word) (hh3 : σ.sh (P 3)=0)
    (hd : σ.sh (P 9)=(σ.st (P 9)).length) (hSC : σ.val (R 1)=0) (hPRE : σ.val (R 2)=0)
    (hcap : σ.val (R 0)+cachesReserve (prefixFields P r)+(originalPrefix r).length+
      2*(frame (termsWord r.terms)).length+10≤cap) :
    WExec cap (headProgram P R) σ (appendO σ (P 9) (R 0) (headBytes P r)) (headClock P r) := by
  have hOS := R.injective.ne (by decide : (0 : Fin 4)≠1)
  have ep := cachesProgram_spec cap (P 9) (R 0) (R 1) hOS (prefixFields P r) σ hsrc hd hSC (by omega)
  let u := appendO σ (P 9) (R 0) ((prefixFields P r).flatMap CacheField.bytes)
  have hb := cachesBytes_le (prefixFields P r)
  have h39 := P.injective.ne (by decide : (3 : Fin 10)≠9)
  have hu3 : u.st (P 3)=r.word := by simp [u, appendO, h39, hs3]
  have et := termsProgram_spec cap (P 3) (P 9) (R 0) (R 1) (R 2) h39 hOS
    (R.injective.ne (by decide : (2 : Fin 4)≠0)) (R.injective.ne (by decide : (2 : Fin 4)≠1))
    (frame (callWord r.header.call))
    (frame ((StagePrint.Header.baseHeaderValues r.header).flatMap natWord))
    r.contextWord (termsWord r.terms) (originalSuffix r) u
    (by rw [hu3]; exact original_split r)
    (by simp [u, appendO, h39, hh3]) (by simp [u, appendO, hd])
    (by simp [u, appendO, R.injective.ne (by decide : (1 : Fin 4)≠0), hSC])
    (by simp [u, appendO, R.injective.ne (by decide : (2 : Fin 4)≠0), hPRE])
    (by
      change u.val (R 0)+(originalPrefix r).length+2*(frame (termsWord r.terms)).length+10≤cap
      simp only [u, appendO_val, Function.update_self]
      omega)
  simpa only [headProgram, prefix_instructions, u, headBytes, headClock, originalPrefix,
    appendO_append] using ep.seq et

end NearQuarticWires.StageTuplePreparedOutput
