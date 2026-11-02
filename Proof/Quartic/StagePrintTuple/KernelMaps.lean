import Proof.Quartic.StagePrintTuple.KernelLayout

set_option autoImplicit false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms
open NearQuarticWires.Control

/-- `lem:print`, paper/paper.tex: a literal
finite list of exterior source tapes embeds unchanged into the fixed
controller tape bank. -/
def kernelExternalMap {k : ℕ} (span : ℕ) (sources : Fin k↪Fin 30) : Fin k↪Fin (span+30) :=
  ⟨fun i=>kernelLocal span (sources i),by
    intro i j h
    exact sources.injective ((kernelLocal span).injective h)⟩

/-- `lem:print`, paper/paper.tex: real source
packet constructors append their exact genuine callee-input tape after
a fixed list of retained exterior sources, without an allocator input. -/
def kernelPacketMap {k : ℕ} (span : ℕ) (sources : Fin k↪Fin 30)
    (p : Program) (hp : p.tapeCount ≤ span) : Fin (k+1)↪Fin (span+30) := by
  let f := kernelExternalMap span sources
  have hsep : ∀j,f j≠(kernelSite span p hp).input := by
    intro j he
    have hh:=congrArg Fin.val he
    change (sources j).val=30 at hh
    have hj:=(sources j).isLt
    omega
  exact ⟨Fin.addCases (fun j=>f j) (fun _ : Fin 1=>(kernelSite span p hp).input),
    addCases_inj f f.injective _ hsep⟩

/-- `lem:print`, paper/paper.tex: the source
part of each packet map has exactly its frozen exterior tape address. -/
theorem kernelPacketMap_source {k : ℕ} (span : ℕ) (sources : Fin k↪Fin 30)
    (p : Program) (hp : p.tapeCount ≤ span) (i : Fin k) :
    kernelPacketMap span sources p hp (Fin.castAdd 1 i)=kernelLocal span (sources i) := by
  simp only [kernelPacketMap,Fin.addCases_left,kernelExternalMap,Function.Embedding.coeFn_mk]

/-- `lem:print`, paper/paper.tex: the last
packet-map tape is the actual fixed input tape of the called program. -/
theorem kernelPacketMap_input {k : ℕ} (span : ℕ) (sources : Fin k↪Fin 30)
    (p : Program) (hp : p.tapeCount ≤ span) :
    kernelPacketMap span sources p hp (Fin.last k)=(kernelSite span p hp).input := by
  change Fin.addCases (m:=k) (n:=1) (motive:=fun _=>Fin (span+30))
    (fun j : Fin k=>kernelLocal span (sources j))
    (fun _ : Fin 1=>(kernelSite span p hp).input) (Fin.last k)=(kernelSite span p hp).input
  have hl : (Fin.last k : Fin (k+1))=Fin.natAdd k (0:Fin 1) := Fin.ext (by simp)
  rw [hl,Fin.addCases_right]

/-- `lem:print`, paper/paper.tex: support
selection uses its actual retained support cache as its only source. -/
def kernelSupportSources : Fin 1↪Fin 30 := ⟨![14],by decide⟩

/-- `lem:print`, paper/paper.tex: native-pool
input construction reads only the real original source, affine header,
context, selected atom cache and computed field-width cache. -/
def kernelNativeSources : Fin 5↪Fin 30 := ⟨![2,3,4,17,11],by decide⟩

/-- `lem:print`, paper/paper.tex: Cartesian
input construction reads exactly the current native pool and tuple
history segment before calling the genuine Cartesian machine. -/
def kernelCartesianSources : Fin 2↪Fin 30 := ⟨![19,20],by decide⟩

/-- `lem:print`, paper/paper.tex: signed Stack
input construction uses the real tuple history and genuine zero,
current-coefficient and two-field caches. -/
def kernelStackSources : Fin 4↪Fin 30 := ⟨![20,7,16,8],by decide⟩

/-- `lem:print`, paper/paper.tex: source-local
support formatting uses nine fixed scratch registers separate from all
persistent tuple and remaining-support counters. -/
def kernelSupportRegisters : Fin 9↪Fin 32 :=
  ⟨fun i=>⟨i.val,by omega⟩,by intro i j h;exact Fin.ext (congrArg (fun x : Fin 32=>x.val) h)⟩

/-- `lem:print`, paper/paper.tex: the two real
native-input copy counters are source-local and reset after each packet. -/
def kernelNativeRegisters : Fin 2↪Fin 32 := ⟨![0,1],by decide⟩

end NearQuarticWires.StageTuple
