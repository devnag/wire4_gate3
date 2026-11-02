import Proof.Quartic.StagePrintTuple.PreparedLoad
import Proof.Wire_3_5.PrimAsmParseNat

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearQuarticWires.StageTuple

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats

/-- `lem:print`, paper/paper.tex: after the real
prepared-word loader, all thirteen actual retained source tapes have
zero cursors and every finite cache and call bank is blank. -/
def kernelLoadedState (span : ℕ) (r : TermCutRequest) : WState (span+29) 32 :=
  ⟨fun _=>0,fun i=>if h:i.val < 13 then r.preparedLoadedSource ⟨i.val,h⟩ else [],fun _=>0,false⟩

/-- `lem:print`, paper/paper.tex: the main
controller reads the physically emitted width and row count and the
actual serialized Terms count, then writes its real initial empty-tuple
delimiter. No decoded scalar or tuple is supplied as a runtime input. -/
def kernelInitializeProgram (span : ℕ) : WM (span+29) 32 :=
  .seq (readNatM false (kernelLocal span 6) 0 1 10 2 3)
    (.seq (readNatM false (kernelLocal span 9) 0 1 11 2 3)
      (.seq (readNatM false (kernelLocal span 5) 0 1 17 2 3)
        (.seq (emitC (kernelLocal span 20) 0 false) (WM.rewind (kernelLocal span 20) 0))))

/-- `lem:print`, paper/paper.tex: the literal
initial loop state has its genuine first monomial cursor, computed
remaining count, singleton empty tuple and empty signed cut output. -/
def kernelInitialData (r : TermCutRequest) : KernelData where
  termCursor := (natWord r.terms.length).length
  remaining := r.terms.length
  caches := fun _=>[]
  cacheHeads := fun _=>0
  history := [false]
  historyHead := 0
  output := []
  stride := 0
  children := 0
  tuples := 0
  reverseIndex := 0
  supportCard := 0

/-- `prop:time`, paper/paper.tex: a real
natural-codec decoder clock is charged for each of the three parsed
scalars, including the one-time complete Terms count. -/
def scalarReadCost (j : ℕ) : ℕ :=
  (natBitLength j+2)*(40*2^(natBitLength j)+40)

/-- `prop:time`, paper/paper.tex: initialization
includes every physical scalar decoder, initial delimiter write and
its actual byte-counter rewind. -/
def kernelInitializeCost (r : TermCutRequest) : ℕ :=
  scalarReadCost (r.stackWidth+1)+scalarReadCost (r.rowDimension+1)+
    scalarReadCost r.terms.length+17

/-- `lem:print` and `prop:time`, paper/paper.tex: genuine encoded source scalars establish the complete
literal initial state for the whole monomial loop. -/
theorem kernelInitializeProgram_spec (cap span : ℕ) (r : TermCutRequest)
    (hL : 2^(natBitLength (r.stackWidth+1)+1) ≤ cap)
    (hN : 2^(natBitLength (r.rowDimension+1)+1) ≤ cap)
    (hT : 2^(natBitLength r.terms.length+1) ≤ cap) (hone : 1 ≤ cap) :
    WExec cap (kernelInitializeProgram span) (kernelLoadedState span r)
      ((kernelInitialData r).state span r) (kernelInitializeCost r) := by
  let σ := kernelLoadedState span r
  have eL := readNatM_spec cap false (kernelLocal span 6) (0:Fin 32) 1 10 2 3
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (r.stackWidth+1) [] [] σ
    (by simp [σ,kernelLoadedState,kernelLocal,TermCutRequest.preparedLoadedSource,
      TermCutRequest.preparedFields,NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc]) rfl rfl rfl rfl rfl (by simpa [σ,kernelLoadedState] using hL)
  let a := (σ.seth (kernelLocal span 6) (natWord (r.stackWidth+1)).length).setv 10 (r.stackWidth+1)
  have eL' : WExec cap (readNatM false (kernelLocal span 6) 0 1 10 2 3) σ a
      (scalarReadCost (r.stackWidth+1)) := by simpa [a,σ,kernelLoadedState,stp,scalarReadCost] using eL
  have eN := readNatM_spec cap false (kernelLocal span 9) (0:Fin 32) 1 11 2 3
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (r.rowDimension+1) [] [] a
    (by simp [a,σ,kernelLoadedState,kernelLocal,TermCutRequest.preparedLoadedSource,
      TermCutRequest.preparedFields,NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc])
    (by simp [a,σ,kernelLoadedState,kernelLocal]) (by simp [a,σ,kernelLoadedState])
    (by simp [a,σ,kernelLoadedState]) (by simp [a,σ,kernelLoadedState])
    (by simp [a,σ,kernelLoadedState]) (by simpa [a,σ,kernelLoadedState] using hN)
  let b := (a.seth (kernelLocal span 9) (natWord (r.rowDimension+1)).length).setv 11 (r.rowDimension+1)
  have eN' : WExec cap (readNatM false (kernelLocal span 9) 0 1 11 2 3) a b
      (scalarReadCost (r.rowDimension+1)) := by simpa [b,a,σ,kernelLoadedState,stp,scalarReadCost] using eN
  have eT := readNatM_spec cap false (kernelLocal span 5) (0:Fin 32) 1 17 2 3
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) r.terms.length [] (r.terms.flatMap monoWord) b
    (by simp [b,a,σ,kernelLoadedState,kernelLocal,TermCutRequest.preparedLoadedSource,
      TermCutRequest.preparedFields,termsWord,listWord,NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc])
    (by simp [b,a,σ,kernelLoadedState,kernelLocal]) (by simp [b,a,σ,kernelLoadedState])
    (by simp [b,a,σ,kernelLoadedState]) (by simp [b,a,σ,kernelLoadedState])
    (by simp [b,a,σ,kernelLoadedState]) (by simpa [b,a,σ,kernelLoadedState] using hT)
  let c := (b.seth (kernelLocal span 5) (natWord r.terms.length).length).setv 17 r.terms.length
  have eT' : WExec cap (readNatM false (kernelLocal span 5) 0 1 17 2 3) b c
      (scalarReadCost r.terms.length) := by simpa [c,b,a,σ,kernelLoadedState,stp,scalarReadCost] using eT
  have eD := NearCubicGates.Close.Codec.emitBit_spec cap (kernelLocal span 20) (0:Fin 32) false c
    (by simp [c,b,a,σ,kernelLoadedState,kernelLocal])
    (by simp [c,b,a,σ,kernelLoadedState];omega)
  let d := appendO c (kernelLocal span 20) 0 [false]
  have eR := wrewind_spec cap (kernelLocal span 20) (0:Fin 32) 1 d
    (by simp [d,c,b,a,appendO,σ,kernelLoadedState])
    (by simp [d,c,b,a,appendO,σ,kernelLoadedState];exact hone)
  refine (eL'.seq (eN'.seq (eT'.seq (eD.seq eR)))).cast cap ?_ (by unfold kernelInitializeCost;omega)
  apply WState.eq
  · funext i
    simp only [KernelData.state,kernelInitialData]
    by_cases h5:i.val=5
    · have hi:i=kernelLocal span 5 := Fin.ext h5
      subst i;simp [d,c,b,a,appendO,σ,kernelLoadedState,kernelLocal]
    · by_cases h6:i.val=6
      · have hi:i=kernelLocal span 6 := Fin.ext h6
        subst i;simp [d,c,b,a,appendO,σ,kernelLoadedState,kernelLocal]
      · by_cases h9:i.val=9
        · have hi:i=kernelLocal span 9 := Fin.ext h9
          subst i;simp [d,c,b,a,appendO,σ,kernelLoadedState,kernelLocal]
        · simp [d,c,b,a,appendO,σ,kernelLoadedState,kernelLocal,Function.update_apply,Fin.ext_iff,h5,h6,h9]
  · funext i
    by_cases h20:i.val=20
    · have hi:i=kernelLocal span 20 := Fin.ext h20
      subst i;simp [d,c,b,a,appendO,σ,kernelLoadedState,kernelLocal,KernelData.state,kernelInitialData]
    · simp [d,c,b,a,appendO,σ,kernelLoadedState,kernelLocal,KernelData.state,kernelInitialData,
        Function.update_apply,Fin.ext_iff,h20]
  · funext i
    fin_cases i <;> simp [d,c,b,a,appendO,σ,kernelLoadedState,KernelData.state,kernelInitialData]
  · rfl

end NearQuarticWires.StageTuple
