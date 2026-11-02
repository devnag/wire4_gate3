import Proof.Quartic.StageNativeKidsPool.Occurrence

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageNativeKidsPool
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close NearCubicGates.Close.WordPrograms
open NearQuarticWires.Control

variable {ns nr : ℕ}

/-- `lem:print`, paper/paper.tex: the
counted original-row loop has a reusable bank and disjoint retained
source, header, accumulated output and scalar loop counters. -/
structure Layout (p : Program) (ns nr : ℕ) where
  site : Site p ns nr
  sources : Fin 3 ↪ Fin (ns+1)
  registers : Fin 5 ↪ Fin nr
  out : Fin (ns+1)
  outputCounter : Fin nr
  remaining : Fin nr
  input_eq : sources 2=site.input
  out_bank : ∀j,site.bank j≠out
  out_tally : out≠site.tally
  out_guard : out≠site.guard
  out_ruler : out≠site.ruler
  out_sources : ∀i,out≠sources i
  counter_registers : ∀i,outputCounter≠registers i
  counter_call : ∀i,outputCounter≠site.regs i
  remaining_registers : ∀i,remaining≠registers i
  remaining_call : ∀i,remaining≠site.regs i
  index_call : ∀i,registers 0≠site.regs i
  remaining_output : remaining≠outputCounter

/-- `lem:print`, paper/paper.tex: every
original row begins with the actual retained sources and an empty
reusable call bank, while all other loaded source fields remain intact. -/
structure Ready {p : Program} (L : Layout p ns nr) (source header : List Bool)
    (j left : ℕ) (σ : WState ns nr) : Prop where
  bank : ∀k,σ.st (L.site.bank k)=[]
  heads : ∀k,σ.sh (L.site.bank k)=0
  tally : σ.st L.site.tally=[]
  tally_head : σ.sh L.site.tally=0
  guard : σ.st L.site.guard=[]
  guard_head : σ.sh L.site.guard=0
  ruler : Worker.Blank (σ.st L.site.ruler)
  ruler_head : σ.sh L.site.ruler=0
  call_registers : ∀i,σ.val (L.site.regs i)=0
  index : σ.val (L.registers 0)=j
  scratch : ∀i,i≠0→σ.val (L.registers i)=0
  source : σ.st (L.sources 0)=frame source
  header : σ.st (L.sources 1)=frame header
  source_heads : ∀i,σ.sh (L.sources i)=0
  out_head : σ.sh L.out=(σ.st L.out).length
  count : σ.val L.remaining=left

/-- `lem:print`, paper/paper.tex: decrementing
the actual positive remaining count preserves every row-call invariant. -/
theorem Ready.dec {p : Program} {L : Layout p ns nr} {source header : List Bool}
    {j left : ℕ} {σ : WState ns nr} (h : Ready L source header j (left+1) σ) :
    Ready L source header j left (σ.setv L.remaining left) := by
  refine ⟨h.bank,h.heads,h.tally,h.tally_head,h.guard,h.guard_head,h.ruler,h.ruler_head,
    ?_,?_,?_,h.source,h.header,h.source_heads,h.out_head,by simp⟩
  · intro i;simpa [Function.update_of_ne (L.remaining_call i).symm] using h.call_registers i
  · simpa [Function.update_of_ne (L.remaining_registers 0).symm] using h.index
  · intro i hi;simpa [Function.update_of_ne (L.remaining_registers i).symm] using h.scratch i hi

/-- `lem:print`, paper/paper.tex: one
completed row appends only its actual raw field bytes and advances the
original child index, preserving the exact retained sources and bank. -/
theorem Ready.next {p : Program} {L : Layout p ns nr} {source header : List Bool}
    {j left : ℕ} {σ : WState ns nr} (h : Ready L source header j left σ) (bits : List Bool) :
    Ready L source header (j+1) left
      ((appendO σ L.out L.outputCounter bits).setv (L.registers 0) (j+1)) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,by simp,?_,?_,?_,?_,?_,?_⟩
  · intro k;simp [appendO,Function.update_of_ne (L.out_bank k),h.bank]
  · intro k;simp [appendO,Function.update_of_ne (L.out_bank k),h.heads]
  · simpa [appendO,Function.update_of_ne L.out_tally.symm] using h.tally
  · simpa [appendO,Function.update_of_ne L.out_tally.symm] using h.tally_head
  · simpa [appendO,Function.update_of_ne L.out_guard.symm] using h.guard
  · simpa [appendO,Function.update_of_ne L.out_guard.symm] using h.guard_head
  · simpa [appendO,Function.update_of_ne L.out_ruler.symm] using h.ruler
  · simpa [appendO,Function.update_of_ne L.out_ruler.symm] using h.ruler_head
  · intro i;simp [appendO,Function.update_of_ne (L.index_call i).symm,
      Function.update_of_ne (L.counter_call i).symm,h.call_registers]
  · intro i hi;simp [appendO,Function.update_of_ne (L.registers.injective.ne hi),
      Function.update_of_ne (L.counter_registers i).symm,h.scratch i hi]
  · simpa [appendO,Function.update_of_ne (L.out_sources 0).symm] using h.source
  · simpa [appendO,Function.update_of_ne (L.out_sources 1).symm] using h.header
  · intro i;simpa [appendO,Function.update_of_ne (L.out_sources i).symm] using h.source_heads i
  · simp [appendO,h.out_head]
  · simpa [appendO,Function.update_of_ne (L.remaining_registers 0),
      Function.update_of_ne L.remaining_output] using h.count

end NearQuarticWires.StageNativeKidsPool
