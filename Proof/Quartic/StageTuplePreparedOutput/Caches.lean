import Proof.Quartic.StageTuplePreparedOutput.Terms
import Proof.Quartic.StagePrintTuple.NestedField

set_option autoImplicit false

namespace NearQuarticWires.StageTuplePreparedOutput

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.WordPrograms
open StageTuple

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: a retained
frame supplies an ordinary or nested output field, with its source
address and mathematical payload distinguished from program control. -/
structure CacheField (ns : ℕ) where
  source : Fin (ns+1)
  bits : List Bool
  nested : Bool

/-- `lem:print`, paper/paper.tex: only a
source address and fixed framing choice are part of each program instruction. -/
def CacheField.instruction (f : CacheField ns) : Fin (ns+1)×Bool := (f.source,f.nested)

/-- `lem:print`, paper/paper.tex: copied
field bytes retain every genuine source marker and required outer layer. -/
def CacheField.bytes (f : CacheField ns) : List Bool :=
  if f.nested then marks (frame (frame f.bits)) else marks (frame f.bits)

/-- `prop:time`, paper/paper.tex: actual
cache copying and source rewinding have their retained literal clocks. -/
def CacheField.clock (f : CacheField ns) : ℕ :=
  if f.nested then appendNestedFieldCost f.bits else appendMarkedFrameCost f.bits

/-- `prop:time`, paper/paper.tex: a linear
byte reserve covers either actual output-framing choice. -/
def CacheField.reserve (f : CacheField ns) : ℕ := 4*((frame f.bits).length+1)

/-- `prop:time`, paper/paper.tex: each
emitted actual cache field fits its declared linear byte reserve. -/
theorem CacheField.bytes_le (f : CacheField ns) : f.bytes.length ≤ f.reserve := by
  cases h : f.nested <;> simp [CacheField.bytes, h, CacheField.reserve, frame_length] <;> omega

/-- `lem:print`, paper/paper.tex: a fixed
finite list of retained cache addresses is copied with the prescribed
ordinary or nested framing and with every source cursor reset. -/
def cachesProgram (instructions : List (Fin (ns+1)×Bool)) (dst : Fin (ns+1))
    (OP SC : Fin nr) : WM ns nr :=
  match instructions with
  | [] => .skip
  | (src,nested)::rest => .seq
      (if nested then appendNestedFieldReset src dst OP SC else appendMarkedFrameReset src dst OP SC)
      (cachesProgram rest dst OP SC)

/-- `prop:time`, paper/paper.tex: actual
cache clocks include all finite sequence transitions and the final halt. -/
def cachesClock (fields : List (CacheField ns)) : ℕ :=
  fields.foldr (fun f t => f.clock+1+t) 1

/-- `prop:time`, paper/paper.tex: the
complete retained cache reserve is additive in actual finite cache bytes. -/
def cachesReserve (fields : List (CacheField ns)) : ℕ := (fields.map CacheField.reserve).sum

/-- `lem:print` and `prop:time`, paper/paper.tex: all retained cache fields are physically
copied with exact framing and full source/scratch restoration; repeated
source caches remain valid because every individual cursor is reset. -/
theorem cachesProgram_spec (cap : ℕ) (dst : Fin (ns+1)) (OP SC : Fin nr) (hOS : OP≠SC)
    (fields : List (CacheField ns)) (σ : WState ns nr)
    (hsrc : ∀ f∈fields, f.source≠dst ∧ σ.st f.source=frame f.bits ∧ σ.sh f.source=0)
    (hd : σ.sh dst=(σ.st dst).length) (hSC : σ.val SC=0)
    (hcap : σ.val OP+cachesReserve fields+1≤cap) :
    WExec cap (cachesProgram (fields.map CacheField.instruction) dst OP SC) σ
      (appendO σ dst OP (fields.flatMap CacheField.bytes)) (cachesClock fields) := by
  induction fields generalizing σ with
  | nil =>
    simpa only [List.map_nil, cachesProgram, cachesClock, List.foldr_nil,
      List.flatMap_nil, appendO_nil] using (WExec.skip (cap:=cap) σ).mono (by decide : 0≤1)
  | cons f fs ih =>
    obtain ⟨hsd, hs, hh⟩ := hsrc f (by simp)
    have hr : f.reserve+cachesReserve fs=cachesReserve (f::fs) := by simp [cachesReserve]
    have he : WExec cap
        (if f.nested then appendNestedFieldReset f.source dst OP SC
          else appendMarkedFrameReset f.source dst OP SC) σ
        (appendO σ dst OP f.bytes) f.clock := by
      cases hn : f.nested
      · simpa only [CacheField.bytes, CacheField.clock, hn, Bool.false_eq_true, if_false] using
          appendMarkedFrameReset_spec cap f.source dst OP SC hsd hOS f.bits [] σ
          (by simpa using hs) hh hd hSC
          (by unfold cachesReserve CacheField.reserve at hcap; simp only [List.map_cons, List.sum_cons] at hcap; omega)
      · simpa only [CacheField.bytes, CacheField.clock, hn, if_true] using
          appendNestedFieldReset_spec cap f.source dst OP SC hsd hOS f.bits [] σ
          (by simpa using hs) hh hd hSC
          (by unfold cachesReserve CacheField.reserve at hcap; simp only [List.map_cons, List.sum_cons] at hcap; omega)
    let u := appendO σ dst OP f.bytes
    have hu : ∀ g∈fs, g.source≠dst ∧ u.st g.source=frame g.bits ∧ u.sh g.source=0 := by
      intro g hg
      obtain ⟨hgd, hgs, hgh⟩ := hsrc g (by simp [hg])
      exact ⟨hgd, by simp [u, appendO, hgd, hgs], by simp [u, appendO, hgd, hgh]⟩
    have ht := ih u hu (by simp [u, appendO, hd])
      (by simp [u, appendO, hOS.symm, hSC]) (by
        have hb := f.bytes_le
        simp only [u, appendO_val, Function.update_self]
        omega)
    simpa only [List.map_cons, CacheField.instruction, cachesProgram, cachesClock, List.foldr_cons,
      List.flatMap_cons, u, appendO_append] using he.seq ht

/-- `prop:time`, paper/paper.tex: the
complete finite cache-copy clock is linear in its additive byte reserve. -/
theorem cachesClock_le (fields : List (CacheField ns)) :
    cachesClock fields ≤ 51*(cachesReserve fields+1) := by
  induction fields with
  | nil => simp [cachesClock, cachesReserve]
  | cons f fs ih =>
    have hf : f.clock+1 ≤ 51*f.reserve := by
      cases hn : f.nested <;>
        simp [CacheField.clock, hn, CacheField.reserve, appendNestedFieldCost, appendMarkedFrameCost] <;> omega
    simp only [cachesClock, List.foldr_cons, cachesReserve, List.map_cons, List.sum_cons] at *
    omega

/-- `prop:time`, paper/paper.tex: the
actual emitted cache bytes fit the same additive linear reserve. -/
theorem cachesBytes_le (fields : List (CacheField ns)) :
    (fields.flatMap CacheField.bytes).length ≤ cachesReserve fields := by
  induction fields with
  | nil => simp [cachesReserve]
  | cons f fs ih =>
    have hf := f.bytes_le
    simp only [List.flatMap_cons, List.length_append, cachesReserve, List.map_cons, List.sum_cons] at *
    omega

end NearQuarticWires.StageTuplePreparedOutput
